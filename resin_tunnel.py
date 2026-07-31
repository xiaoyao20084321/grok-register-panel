#!/usr/bin/env python
# -*- coding: utf-8 -*-
"""独立管理 Resin 服务的 SSH 本地端口转发。

该模块不依赖邮箱服务商。启用自动隧道时，它会验证本地代理地址、复用已经
可访问 Resin `/healthz` 的外部隧道，或启动仅由当前进程持有的 SSH 子进程。
"""

from __future__ import annotations

import atexit
import http.client
import json
import os
import socket
import stat
import subprocess
import threading
import time
from pathlib import Path
from typing import Any, Callable, Dict, Optional
from urllib.parse import urlsplit


# DEFAULT_SSH_KEY 是 Resin 自动隧道默认使用的本机 SSH 私钥路径。
DEFAULT_SSH_KEY = "~/.ssh/MaXiangLinTxCloudMiYao.pem"
# DEFAULT_SSH_USER 是连接云服务器时默认使用的系统账号。
DEFAULT_SSH_USER = "ubuntu"
# DEFAULT_LOCAL_PORT 是 Resin 服务映射到本机后的默认监听端口。
DEFAULT_LOCAL_PORT = 12260
# DEFAULT_REMOTE_PORT 是云服务器回环地址上 Resin 的默认监听端口。
DEFAULT_REMOTE_PORT = 2260
# DEFAULT_TUNNEL_TIMEOUT 是等待 SSH 建立并通过 Resin 健康检查的最长秒数。
DEFAULT_TUNNEL_TIMEOUT = 15


class ResinTunnelConfigError(ValueError):
    """表示 Resin SSH 隧道字段缺失、端口无效或代理入口不匹配。"""


class ResinTunnelError(RuntimeError):
    """表示 Resin 隧道启动、复用或健康检查阶段发生运行时故障。"""


def _parse_port(value: Any, field_name: str, default: int) -> int:
    """把配置值转换成有效 TCP 端口，失败时返回可直接展示的中文错误。"""
    try:
        port = int(value or default)
    except (TypeError, ValueError) as exc:
        raise ResinTunnelConfigError(f"{field_name} 必须是整数") from exc
    if not 1 <= port <= 65535:
        raise ResinTunnelConfigError(f"{field_name} 必须在 1-65535 之间")
    return port


def _normalize_config(config: Dict[str, Any]) -> Dict[str, Any]:
    """提取并校验 Resin 隧道配置，不保存 Token 或其他代理认证信息。"""
    enabled = bool(config.get("resin_enable_tunnel", False))
    if not enabled:
        # 自动隧道关闭时 SSH 字段完全不参与校验，兼容本机或外部代理入口。
        return {
            "enabled": False,
            "ssh_key": "",
            "ssh_user": "",
            "ssh_host": "",
            "local_port": DEFAULT_LOCAL_PORT,
            "remote_port": DEFAULT_REMOTE_PORT,
            "timeout": DEFAULT_TUNNEL_TIMEOUT,
            "proxy": str(config.get("proxy", "") or "").strip(),
        }

    local_port = _parse_port(
        config.get("resin_local_port"),
        "Resin 本地端口",
        DEFAULT_LOCAL_PORT,
    )
    remote_port = _parse_port(
        config.get("resin_remote_port"),
        "Resin 远端端口",
        DEFAULT_REMOTE_PORT,
    )
    try:
        timeout = max(
            int(
                config.get("resin_tunnel_timeout", DEFAULT_TUNNEL_TIMEOUT)
                or DEFAULT_TUNNEL_TIMEOUT
            ),
            1,
        )
    except (TypeError, ValueError) as exc:
        raise ResinTunnelConfigError("Resin 隧道超时必须是整数") from exc

    normalized = {
        "enabled": enabled,
        "ssh_key": str(
            config.get("resin_ssh_key", DEFAULT_SSH_KEY) or DEFAULT_SSH_KEY
        ),
        "ssh_user": str(
            config.get("resin_ssh_user", DEFAULT_SSH_USER) or DEFAULT_SSH_USER
        ).strip(),
        "ssh_host": str(config.get("resin_ssh_host", "") or "").strip(),
        "local_port": local_port,
        "remote_port": remote_port,
        "timeout": timeout,
        "proxy": str(config.get("proxy", "") or "").strip(),
    }
    try:
        parsed_proxy = urlsplit(normalized["proxy"])
        proxy_port = parsed_proxy.port
    except ValueError as exc:
        raise ResinTunnelConfigError(f"Resin 代理地址无效: {exc}") from exc
    if parsed_proxy.hostname not in ("127.0.0.1", "localhost", "::1"):
        raise ResinTunnelConfigError(
            "开启 Resin 自动隧道时，代理地址主机必须是 127.0.0.1 或 localhost"
        )
    if proxy_port != local_port:
        raise ResinTunnelConfigError(
            f"Resin 代理地址端口必须与本地端口一致，应填写 "
            f"http://127.0.0.1:{local_port}"
        )
    return normalized


def _probe_resin_health(local_port: int) -> bool:
    """通过无需认证的 `/healthz` 判断本地端口后面是否确实为 Resin。"""
    connection: Optional[http.client.HTTPConnection] = None
    try:
        connection = http.client.HTTPConnection(
            "127.0.0.1",
            int(local_port),
            timeout=1.5,
        )
        connection.request("GET", "/healthz", headers={"Connection": "close"})
        response = connection.getresponse()
        body = response.read(512)
        if int(response.status or 0) != 200:
            return False
        payload = json.loads(body.decode("utf-8", errors="replace"))
        return (
            isinstance(payload, dict)
            and str(payload.get("status", "") or "").lower() == "ok"
        )
    except Exception:
        return False
    finally:
        if connection is not None:
            try:
                connection.close()
            except Exception:
                pass


def _tcp_port_open(local_port: int) -> bool:
    """判断本机端口是否已被监听，用于区分端口占用和 SSH 启动失败。"""
    try:
        with socket.create_connection(("127.0.0.1", int(local_port)), timeout=1):
            return True
    except OSError:
        return False


class ResinTunnelManager:
    """串行管理当前进程创建的 Resin SSH 隧道及其生命周期。"""

    def __init__(self) -> None:
        """初始化线程锁和自有 SSH 子进程状态，不主动建立网络连接。"""
        # _lock 防止 GUI 检查和注册启动同时创建两个相同的 SSH 隧道。
        self._lock = threading.RLock()
        # _process 只保存当前进程创建的 SSH 子进程，绝不记录外部隧道。
        self._process: Optional[subprocess.Popen] = None
        # _fingerprint 标识自有隧道对应的主机、用户、私钥和端口组合。
        self._fingerprint = ""

    def ensure(
        self,
        config: Dict[str, Any],
        log_callback: Optional[Callable[[str], None]] = None,
    ) -> bool:
        """确保 Resin 本地入口可用；返回本次是否创建了新的 SSH 子进程。

        自动隧道关闭时不修改外部连接。自动隧道开启时会优先复用健康的 Resin
        入口；若端口被非 Resin 程序占用则直接报错，避免误连接其他本地服务。
        """
        normalized = _normalize_config(config)
        if not bool(normalized["enabled"]):
            with self._lock:
                # 用户关闭自动隧道后回收本进程旧转发，外部手动隧道不受影响。
                self._terminate_owned_process()
            return False

        fingerprint = "|".join(
            (
                str(
                    Path(
                        os.path.expandvars(str(normalized["ssh_key"]))
                    ).expanduser()
                ),
                str(normalized["ssh_user"]),
                str(normalized["ssh_host"]),
                str(normalized["local_port"]),
                str(normalized["remote_port"]),
            )
        )
        with self._lock:
            process = self._process
            if (
                process is not None
                and process.poll() is None
                and self._fingerprint != fingerprint
            ):
                # 配置变化后只回收本进程旧隧道，避免旧端口继续占用和误复用。
                self._terminate_owned_process()
                process = None
            elif process is not None and process.poll() is not None:
                self._process = None
                self._fingerprint = ""
                process = None

            local_port = int(normalized["local_port"])
            if _probe_resin_health(local_port):
                if log_callback:
                    log_callback(
                        f"[*] Resin SSH 隧道已可用，复用本地入口 "
                        f"127.0.0.1:{local_port}"
                    )
                return False

            if process is not None and process.poll() is None:
                try:
                    self._wait_for_health(
                        process,
                        local_port,
                        int(normalized["timeout"]),
                    )
                except Exception:
                    self._terminate_owned_process()
                    raise
                return False

            if _tcp_port_open(local_port):
                raise ResinTunnelError(
                    f"本地端口 {local_port} 已被占用，但 /healthz 不是可用的 Resin"
                )

            self._start_tunnel(normalized)
            self._fingerprint = fingerprint
            if log_callback:
                log_callback(
                    f"[*] Resin SSH 隧道已建立: "
                    f"127.0.0.1:{local_port} -> "
                    f"{normalized['ssh_host']}:{normalized['remote_port']}"
                )
            return True

    def shutdown(self) -> None:
        """关闭仅由当前进程创建的 Resin SSH 隧道，不影响手动建立的隧道。"""
        with self._lock:
            self._terminate_owned_process()

    def _terminate_owned_process(self) -> None:
        """终止并清空当前进程持有的 SSH 子进程；调用方必须持有管理锁。"""
        process = self._process
        self._process = None
        self._fingerprint = ""
        if process is None or process.poll() is not None:
            return
        try:
            process.terminate()
            process.wait(timeout=3)
        except Exception:
            try:
                process.kill()
                process.wait(timeout=1)
            except Exception:
                pass

    def _start_tunnel(self, normalized: Dict[str, Any]) -> None:
        """按规范化配置启动 SSH 端口转发，并等待 Resin 健康检查成功。"""
        if not normalized["ssh_host"]:
            raise ResinTunnelConfigError(
                "已开启 Resin 自动隧道，但未填写 SSH 主机"
            )
        if not normalized["ssh_user"]:
            raise ResinTunnelConfigError(
                "已开启 Resin 自动隧道，但未填写 SSH 用户"
            )
        key_path = Path(
            os.path.expandvars(str(normalized["ssh_key"]))
        ).expanduser()
        if not key_path.is_file():
            raise ResinTunnelConfigError(f"Resin SSH 私钥不存在: {key_path}")
        try:
            os.chmod(key_path, stat.S_IRUSR)
        except OSError as exc:
            raise ResinTunnelError(f"设置 Resin SSH 私钥权限失败: {exc}") from exc

        command = [
            "ssh",
            "-i",
            str(key_path),
            "-o",
            "IdentitiesOnly=yes",
            "-o",
            "ExitOnForwardFailure=yes",
            "-o",
            "BatchMode=yes",
            "-o",
            "ServerAliveInterval=60",
            "-N",
            "-L",
            (
                f"{normalized['local_port']}:127.0.0.1:"
                f"{normalized['remote_port']}"
            ),
            f"{normalized['ssh_user']}@{normalized['ssh_host']}",
        ]
        try:
            process = subprocess.Popen(
                command,
                stdin=subprocess.DEVNULL,
                stdout=subprocess.DEVNULL,
                stderr=subprocess.PIPE,
                text=True,
            )
        except Exception as exc:
            raise ResinTunnelError(f"启动 Resin SSH 隧道失败: {exc}") from exc

        self._process = process
        try:
            self._wait_for_health(
                process,
                int(normalized["local_port"]),
                int(normalized["timeout"]),
            )
        except Exception:
            self._terminate_owned_process()
            raise

    def _wait_for_health(
        self,
        process: subprocess.Popen,
        local_port: int,
        timeout: int,
    ) -> None:
        """等待 Resin `/healthz` 成功，并提取 SSH 提前退出时的精简错误。"""
        deadline = time.time() + max(int(timeout), 1)
        while time.time() < deadline:
            if _probe_resin_health(local_port):
                return
            if process.poll() is not None:
                stderr = ""
                try:
                    stderr = str(
                        process.stderr.read() if process.stderr else ""
                    ).strip()
                except Exception:
                    stderr = ""
                raise ResinTunnelError(
                    f"Resin SSH 隧道提前退出，code={process.returncode}: "
                    f"{stderr[:300]}"
                )
            time.sleep(0.25)
        raise ResinTunnelError(
            f"Resin SSH 隧道已启动，但 {timeout}s 内 "
            f"127.0.0.1:{local_port}/healthz 未就绪"
        )


# _MANAGER 是整个注册机进程共享的 Resin SSH 隧道管理器。
_MANAGER = ResinTunnelManager()


def validate_config(config: Dict[str, Any]) -> None:
    """校验 Resin 自动隧道字段，不建立 SSH 连接或修改本地端口。"""
    _normalize_config(config)


def ensure(
    config: Dict[str, Any],
    log_callback: Optional[Callable[[str], None]] = None,
) -> bool:
    """建立或复用 Resin SSH 隧道，并返回本次是否创建了子进程。"""
    return _MANAGER.ensure(config, log_callback)


def shutdown() -> None:
    """关闭全局管理器创建的 Resin SSH 隧道，不影响外部 SSH 进程。"""
    _MANAGER.shutdown()


# 正常退出时只回收当前 Python 进程自己创建的 Resin SSH 隧道。
atexit.register(shutdown)

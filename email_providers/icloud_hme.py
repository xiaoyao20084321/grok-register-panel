"""iCloud Hide My Email 邮箱提供商。

本模块负责通过本地 SSH 隧道访问 icloud-hme 服务，完成账号轮询、
隐私邮箱创建和验证码轮询。创建后的别名会永久保留，不因注册结果而删除。
"""

from __future__ import annotations

import atexit
import datetime as _datetime
import json
import os
import stat
import subprocess
import threading
import time
import uuid
from pathlib import Path
from typing import Any, Callable, Dict, List, Optional, Tuple
from urllib.parse import urlparse

import requests

from email_providers.common import extract_verification_code


# 默认 API 地址指向 SSH 隧道在本机监听的端口，避免将 icloud-hme 暴露到公网。
DEFAULT_API_BASE = "http://127.0.0.1:18090"
# 默认 SSH 私钥路径与用户现有云服务器配置保持一致。
DEFAULT_SSH_KEY = "~/.ssh/MaXiangLinTxCloudMiYao.pem"
# 默认 SSH 登录用户使用云服务器的 ubuntu 账号。
DEFAULT_SSH_USER = "ubuntu"
# 默认远端主机留空，要求示例配置或用户配置显式提供。
DEFAULT_SSH_HOST = ""
# 默认本地转发端口与 API 地址保持一致。
DEFAULT_LOCAL_PORT = 18090
# 默认远端端口对应服务器上仅监听回环地址的 icloud-hme 服务。
DEFAULT_REMOTE_PORT = 8090
# API 请求超时用于避免邮箱线程因隧道或服务故障永久阻塞。
DEFAULT_REQUEST_TIMEOUT = 30
# 隧道启动等待时间覆盖 SSH 握手和远端服务首次响应。
DEFAULT_TUNNEL_TIMEOUT = 15
# 租约文件版本用于后续兼容持久化结构升级。
LEASE_STORE_VERSION = 1


class ICloudHMEError(RuntimeError):
    """表示 iCloud HME API、SSH 隧道或别名生命周期操作失败。"""


class ICloudHMEAddressLimitError(ICloudHMEError):
    """表示所有可用 iCloud 账号当前都无法继续创建隐藏邮箱地址。"""


class ICloudHMEProvider:
    """管理 iCloud HME 服务连接、账号轮询和隐私邮箱租约。"""

    def __init__(self, session: Optional[requests.Session] = None) -> None:
        """初始化提供商；测试可注入自定义 HTTP 会话以隔离真实网络。"""
        # 可重入锁串行化配置、账号游标、租约文件和隧道进程状态。
        self._lock = threading.RLock()
        # 线程局部状态保存每个注册 worker 当前占用的隐私邮箱租约。
        self._thread_state = threading.local()
        # HTTP 会话禁用环境代理，确保本机隧道请求不会经过住宅代理。
        self._session = session or requests.Session()
        if hasattr(self._session, "trust_env"):
            self._session.trust_env = False
        # 当前配置快照仅包含运行 icloud-hme 所需字段，不保存 App 专用密码。
        self._config: Dict[str, Any] = {}
        # 租约文件路径由主程序的 accounts 目录注入。
        self._state_path: Optional[Path] = None
        # 日志回调用于把别名创建、保留和隧道状态写入主程序日志。
        self._log_callback: Optional[Callable[[str], None]] = None
        # 账号轮询游标在同一进程内持续递增，并受锁保护。
        self._account_cursor = 0
        # 仅记录由当前进程启动的 SSH 隧道，退出时不会误杀外部隧道。
        self._tunnel_process: Optional[subprocess.Popen] = None
        # 配置指纹用于识别连接配置变化并重置账号轮询游标。
        self._config_fingerprint = ""

    def configure(
        self,
        config: Dict[str, Any],
        state_path: str,
        log_callback: Optional[Callable[[str], None]] = None,
    ) -> None:
        """应用运行配置并指定持久化租约文件，不接收或保存 iCloud 密码。"""
        normalized = {
            "icloud_api_base": str(
                config.get("icloud_api_base", DEFAULT_API_BASE) or DEFAULT_API_BASE
            ).rstrip("/"),
            "icloud_enable_tunnel": bool(config.get("icloud_enable_tunnel", True)),
            "icloud_ssh_key": str(
                config.get("icloud_ssh_key", DEFAULT_SSH_KEY) or DEFAULT_SSH_KEY
            ),
            "icloud_ssh_user": str(
                config.get("icloud_ssh_user", DEFAULT_SSH_USER) or DEFAULT_SSH_USER
            ).strip(),
            "icloud_ssh_host": str(
                config.get("icloud_ssh_host", DEFAULT_SSH_HOST) or DEFAULT_SSH_HOST
            ).strip(),
            "icloud_local_port": int(
                config.get("icloud_local_port", DEFAULT_LOCAL_PORT) or DEFAULT_LOCAL_PORT
            ),
            "icloud_remote_port": int(
                config.get("icloud_remote_port", DEFAULT_REMOTE_PORT) or DEFAULT_REMOTE_PORT
            ),
            "icloud_request_timeout": int(
                config.get("icloud_request_timeout", DEFAULT_REQUEST_TIMEOUT)
                or DEFAULT_REQUEST_TIMEOUT
            ),
            "icloud_tunnel_timeout": int(
                config.get("icloud_tunnel_timeout", DEFAULT_TUNNEL_TIMEOUT)
                or DEFAULT_TUNNEL_TIMEOUT
            ),
        }
        fingerprint = json.dumps(normalized, ensure_ascii=False, sort_keys=True)
        with self._lock:
            if self._config_fingerprint and self._config_fingerprint != fingerprint:
                self._account_cursor = 0
            self._config = normalized
            self._config_fingerprint = fingerprint
            self._state_path = Path(state_path).expanduser().resolve()
            if log_callback is not None:
                self._log_callback = log_callback

    def check_connectivity(self) -> Dict[str, int]:
        """确保隧道和 API 可用，并返回账号数量及可用账号数量。"""
        self._ensure_configured()
        self._ensure_service()
        accounts = self._list_accounts()
        active = [item for item in accounts if self._is_active_account(item)]
        imap_ready = [
            item
            for item in active
            if bool(item.get("imap_ready"))
            or bool(str(item.get("app_password", "") or "").strip())
        ]
        return {
            "accounts": len(accounts),
            "active": len(active),
            "imap_ready": len(imap_ready),
        }

    def create_mailbox(self) -> Tuple[str, str]:
        """轮询活跃账号创建隐私邮箱，全部账号受限时抛出批次终止异常。"""
        self._ensure_configured()
        self._ensure_service()
        self._retain_current_before_reuse()

        accounts = self._ordered_active_accounts()
        limit_errors = []
        for account in accounts:
            account_id = str(account.get("id", "") or "")
            try:
                return self._create_mailbox_for_account(account)
            except ICloudHMEAddressLimitError as exc:
                limit_errors.append(str(exc))
                self._log(
                    f"[!] iCloud 账号 {account_id} 当前创建额度受限"
                    + ("，继续尝试下一个活跃账号" if len(accounts) > 1 else "")
                )

        detail = limit_errors[-1] if limit_errors else "Apple 未返回具体原因"
        raise ICloudHMEAddressLimitError(
            f"全部 {len(accounts)} 个活跃 iCloud 账号均达到当前创建限制: {detail}"
        )

    def _create_mailbox_for_account(
        self,
        account: Dict[str, Any],
    ) -> Tuple[str, str]:
        """使用指定 iCloud 账号创建一个永久保留的隐私邮箱及本地租约。"""
        account_id = str(account.get("id", "") or "")
        lease_id = uuid.uuid4().hex
        label = f"grok-register:{lease_id}"
        lease = {
            "lease_id": lease_id,
            "account_id": account_id,
            "email": "",
            "label": label,
            "status": "creating",
            "created_at": _datetime.datetime.now(
                _datetime.timezone.utc
            ).isoformat(),
        }
        self._save_lease(lease)
        self._thread_state.lease_id = lease_id

        try:
            payload = self._request_json(
                "POST",
                "/api/create",
                json_body={"account_id": account_id, "label": label},
            )
            data = payload.get("data") if isinstance(payload, dict) else None
            email = str((data or {}).get("email", "") or "").strip().lower()
            if not email or "@" not in email:
                raise ICloudHMEError("创建隐私邮箱成功响应缺少有效 email")
            lease["email"] = email
            lease["status"] = "created"
            self._save_lease(lease)

            self._log(
                f"[*] iCloud HME 已创建并保留隐私邮箱，账号={account_id}，邮箱={email}"
            )
            return email, lease_id
        except ICloudHMEAddressLimitError as exc:
            # 明确的额度拒绝不会在 Apple 侧创建别名，仅保留失败记录供审计。
            lease["status"] = "create_limit"
            lease["error"] = str(exc)[:500]
            self._save_lease(lease)
            raise
        except Exception as exc:
            # 创建请求可能已经在 Apple 侧生效；保留租约记录且绝不调用删除接口。
            lease["status"] = "create_uncertain"
            lease["error"] = str(exc)[:500]
            self._save_lease(lease)
            self._log(
                f"[!] iCloud HME 创建流程异常，按保留策略不删除可能已创建的别名: {label}"
            )
            raise

    def wait_for_code(
        self,
        lease_token: str,
        email: str,
        *,
        timeout: int = 180,
        poll_interval: int = 3,
        raise_if_cancelled: Callable[[Optional[Callable[[], bool]]], None],
        sleep_with_cancel: Callable[[float, Optional[Callable[[], bool]]], None],
        log_callback: Optional[Callable[[str], None]] = None,
        cancel_callback: Optional[Callable[[], bool]] = None,
        resend_callback: Optional[Callable[[], None]] = None,
    ) -> str:
        """按隐私邮箱精确轮询 IMAP 收件结果并提取 xAI 验证码。"""
        self._ensure_configured()
        self._ensure_service()
        lease = self._get_lease(str(lease_token or ""))
        if not lease:
            raise ICloudHMEError("iCloud HME 邮箱租约记录不存在")
        expected_email = str(lease.get("email", "") or "").strip().lower()
        if expected_email and expected_email != str(email or "").strip().lower():
            raise ICloudHMEError("iCloud HME 邮箱与租约不匹配")

        account_id = str(lease.get("account_id", "") or "")
        deadline = time.time() + max(int(timeout), 1)
        seen_messages = set()
        next_resend_at = time.time() + 35
        last_error = ""
        while time.time() < deadline:
            raise_if_cancelled(cancel_callback)
            if resend_callback and time.time() >= next_resend_at:
                try:
                    resend_callback()
                    if log_callback:
                        log_callback("[*] 已触发重新发送 iCloud 邮箱验证码")
                except Exception as exc:
                    if log_callback:
                        log_callback(f"[Debug] 触发重发验证码失败: {exc}")
                next_resend_at = time.time() + 35

            try:
                payload = self._request_json(
                    "GET",
                    "/api/inbox",
                    params={
                        "account_id": account_id,
                        "alias": email,
                        "limit": 20,
                        "days": 1,
                    },
                )
                data = payload.get("data") if isinstance(payload, dict) else {}
                method = str((data or {}).get("method", "") or "")
                messages = (data or {}).get("messages") or []
                if method and method != "imap" and log_callback:
                    log_callback(
                        "[Debug] iCloud HME 当前使用 Web API 收信；建议配置 App 专用密码启用 IMAP"
                    )
                for message in messages:
                    if not isinstance(message, dict):
                        continue
                    message_id = str(
                        message.get("id")
                        or f"{message.get('subject', '')}|{message.get('date', '')}"
                    )
                    if message_id in seen_messages:
                        continue
                    seen_messages.add(message_id)
                    subject = str(message.get("subject", "") or "")
                    combined = "\n".join(
                        str(message.get(key, "") or "")
                        for key in ("preview", "body", "from", "to")
                    )
                    code = extract_verification_code(combined, subject)
                    if code:
                        if log_callback:
                            log_callback(
                                f"[*] iCloud HME 从邮件中提取到验证码: {code}"
                            )
                        return code
                last_error = ""
            except Exception as exc:
                last_error = str(exc)
                if log_callback:
                    log_callback(f"[Debug] iCloud HME 拉取邮件失败: {last_error}")
            sleep_with_cancel(max(int(poll_interval), 1), cancel_callback)

        detail = f"，最后错误: {last_error}" if last_error else ""
        raise ICloudHMEError(
            f"iCloud HME 在 {timeout}s 内未收到验证码邮件{detail}"
        )

    def retain_current_alias(
        self,
        log_callback: Optional[Callable[[str], None]] = None,
    ) -> bool:
        """结束当前 worker 的租约占用，但永久保留 Apple 侧隐私邮箱和本地记录。"""
        lease_id = str(getattr(self._thread_state, "lease_id", "") or "")
        if not lease_id:
            return True
        if log_callback is not None:
            self._log_callback = log_callback
        lease = self._get_lease(lease_id) or {}
        self._thread_state.lease_id = ""
        email = str(lease.get("email", "") or "").strip()
        status = str(lease.get("status", "") or "")
        if email:
            self._log(f"[*] iCloud HME 已保留隐私邮箱: {email}")
        elif status == "create_limit":
            self._log("[*] iCloud HME 本次未创建邮箱地址；已保留额度失败记录")
        else:
            self._log("[*] iCloud HME 未取得可确认的邮箱地址；已保留待核对租约记录")
        return True

    def shutdown(self) -> None:
        """关闭仅由当前进程启动的 SSH 隧道，不删除任何隐私邮箱。"""
        with self._lock:
            process = self._tunnel_process
            self._tunnel_process = None
        if process and process.poll() is None:
            try:
                process.terminate()
                process.wait(timeout=3)
            except Exception:
                try:
                    process.kill()
                except Exception:
                    pass

    def _ensure_configured(self) -> None:
        """确认主程序已经注入配置和租约文件路径。"""
        if not self._config or self._state_path is None:
            raise ICloudHMEError("iCloud HME provider 尚未配置")

    def _ensure_service(self) -> None:
        """复用可用服务；不可用且已启用隧道时启动 SSH 本地转发。"""
        if self._probe_api():
            return
        if not bool(self._config.get("icloud_enable_tunnel", True)):
            raise ICloudHMEError(
                f"无法连接 iCloud HME API: {self._api_base()}，且自动 SSH 隧道未启用"
            )

        with self._lock:
            if self._probe_api():
                return
            process = self._tunnel_process
            if process and process.poll() is None:
                self._wait_for_api(process)
                return
            self._start_tunnel()

    def _start_tunnel(self) -> None:
        """按配置启动 SSH 本地端口转发，并等待 icloud-hme API 就绪。"""
        key_path = Path(
            str(self._config.get("icloud_ssh_key", DEFAULT_SSH_KEY))
        ).expanduser()
        host = str(self._config.get("icloud_ssh_host", "") or "").strip()
        user = str(
            self._config.get("icloud_ssh_user", DEFAULT_SSH_USER) or DEFAULT_SSH_USER
        ).strip()
        local_port = int(
            self._config.get("icloud_local_port", DEFAULT_LOCAL_PORT)
            or DEFAULT_LOCAL_PORT
        )
        remote_port = int(
            self._config.get("icloud_remote_port", DEFAULT_REMOTE_PORT)
            or DEFAULT_REMOTE_PORT
        )
        if not host:
            raise ICloudHMEError("自动 SSH 隧道已启用，但未配置 icloud_ssh_host")
        if not key_path.is_file():
            raise ICloudHMEError(f"SSH 私钥不存在: {key_path}")
        os.chmod(key_path, stat.S_IRUSR)

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
            "ServerAliveInterval=30",
            "-N",
            "-L",
            f"{local_port}:127.0.0.1:{remote_port}",
            f"{user}@{host}",
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
            raise ICloudHMEError(f"启动 SSH 隧道失败: {exc}") from exc
        self._tunnel_process = process
        self._wait_for_api(process)
        self._log(
            f"[*] iCloud HME SSH 隧道已建立: 127.0.0.1:{local_port} -> {host}:{remote_port}"
        )

    def _wait_for_api(self, process: subprocess.Popen) -> None:
        """等待隧道后的 API 可用，并在 SSH 提前退出时返回精简错误。"""
        timeout = int(
            self._config.get("icloud_tunnel_timeout", DEFAULT_TUNNEL_TIMEOUT)
            or DEFAULT_TUNNEL_TIMEOUT
        )
        deadline = time.time() + max(timeout, 1)
        while time.time() < deadline:
            if self._probe_api():
                return
            if process.poll() is not None:
                stderr = ""
                try:
                    stderr = str(process.stderr.read() if process.stderr else "").strip()
                except Exception:
                    stderr = ""
                raise ICloudHMEError(
                    f"SSH 隧道提前退出，code={process.returncode}: {stderr[:300]}"
                )
            time.sleep(0.25)
        try:
            process.terminate()
        except Exception:
            pass
        raise ICloudHMEError(
            f"SSH 隧道已启动，但 {timeout}s 内 API 未就绪: {self._api_base()}"
        )

    def _probe_api(self) -> bool:
        """用账号列表接口轻量探测 API，不输出账号隐私字段。"""
        if not self._config:
            return False
        try:
            response = self._session.request(
                "GET",
                f"{self._api_base()}/api/accounts",
                timeout=2,
            )
            if int(getattr(response, "status_code", 0) or 0) != 200:
                return False
            payload = response.json()
            return isinstance(payload, dict) and payload.get("success") is True
        except Exception:
            return False

    def _api_base(self) -> str:
        """返回去除尾部斜杠后的本地 API 地址。"""
        return str(
            self._config.get("icloud_api_base", DEFAULT_API_BASE) or DEFAULT_API_BASE
        ).rstrip("/")

    def _request_json(
        self,
        method: str,
        path: str,
        *,
        params: Optional[Dict[str, Any]] = None,
        json_body: Optional[Dict[str, Any]] = None,
    ) -> Dict[str, Any]:
        """调用 icloud-hme API，统一校验 HTTP 状态和 success 响应字段。"""
        timeout = int(
            self._config.get("icloud_request_timeout", DEFAULT_REQUEST_TIMEOUT)
            or DEFAULT_REQUEST_TIMEOUT
        )
        url = f"{self._api_base()}{path}"
        try:
            response = self._session.request(
                method,
                url,
                params=params,
                json=json_body,
                timeout=max(timeout, 1),
            )
        except Exception as exc:
            raise ICloudHMEError(f"iCloud HME 请求失败 {method} {path}: {exc}") from exc

        status = int(getattr(response, "status_code", 0) or 0)
        try:
            payload = response.json()
        except Exception as exc:
            preview = str(getattr(response, "text", "") or "")[:300]
            raise ICloudHMEError(
                f"iCloud HME 返回非 JSON，HTTP {status}: {preview}"
            ) from exc
        if status >= 400 or not isinstance(payload, dict) or payload.get("success") is not True:
            message = (
                str(payload.get("message", "") or "")
                if isinstance(payload, dict)
                else str(payload)
            )
            detail = f"iCloud HME API 失败，HTTP {status}: {message or '未知错误'}"
            normalized_message = message.casefold()
            if path.rstrip("/") == "/api/create" and (
                "limit of addresses" in normalized_message
                or (
                    "reached the limit" in normalized_message
                    and "address" in normalized_message
                )
            ):
                raise ICloudHMEAddressLimitError(detail)
            raise ICloudHMEError(detail)
        return payload

    def _list_accounts(self) -> List[Dict[str, Any]]:
        """读取账号列表并按创建时间和 ID 固定排序，消除 Go map 顺序抖动。"""
        payload = self._request_json("GET", "/api/accounts")
        data = payload.get("data") or []
        if not isinstance(data, list):
            raise ICloudHMEError("iCloud HME 账号列表格式无效")
        accounts = [item for item in data if isinstance(item, dict)]
        accounts.sort(
            key=lambda item: (
                str(item.get("created_at", "") or ""),
                str(item.get("id", "") or ""),
            )
        )
        return accounts

    def _ordered_active_accounts(self) -> List[Dict[str, Any]]:
        """返回从当前轮询游标开始的全部活跃账号，并推进下一轮起点。"""
        accounts = [
            item for item in self._list_accounts() if self._is_active_account(item)
        ]
        if not accounts:
            raise ICloudHMEError("iCloud HME 没有 status=active 的可用账号")
        with self._lock:
            start = self._account_cursor % len(accounts)
            self._account_cursor = (self._account_cursor + 1) % len(accounts)
        return accounts[start:] + accounts[:start]

    @staticmethod
    def _is_active_account(account: Dict[str, Any]) -> bool:
        """判断账号是否包含有效 ID 且状态为 active。"""
        return (
            str(account.get("status", "") or "").strip().lower() == "active"
            and bool(str(account.get("id", "") or "").strip())
        )

    def _retain_current_before_reuse(self) -> None:
        """创建新邮箱前结束旧租约占用，同时保留旧邮箱及其持久化记录。"""
        self.retain_current_alias()

    def _empty_store(self) -> Dict[str, Any]:
        """返回新的空租约存储结构。"""
        return {"version": LEASE_STORE_VERSION, "leases": {}}

    def _load_store(self) -> Dict[str, Any]:
        """读取租约文件；文件不存在时返回空结构，格式损坏时拒绝覆盖。"""
        self._ensure_configured()
        assert self._state_path is not None
        with self._lock:
            if not self._state_path.exists():
                return self._empty_store()
            try:
                payload = json.loads(self._state_path.read_text(encoding="utf-8"))
            except Exception as exc:
                raise ICloudHMEError(
                    f"iCloud HME 租约文件损坏: {self._state_path}: {exc}"
                ) from exc
            if not isinstance(payload, dict) or not isinstance(
                payload.get("leases"), dict
            ):
                raise ICloudHMEError(
                    f"iCloud HME 租约文件格式无效: {self._state_path}"
                )
            return payload

    def _write_store(self, payload: Dict[str, Any]) -> None:
        """以原子替换和 0600 权限写入租约文件，避免进程中断产生半文件。"""
        self._ensure_configured()
        assert self._state_path is not None
        with self._lock:
            self._state_path.parent.mkdir(parents=True, exist_ok=True)
            temporary = self._state_path.with_name(
                f".{self._state_path.name}.{os.getpid()}.tmp"
            )
            text = json.dumps(payload, ensure_ascii=False, indent=2, sort_keys=True)
            with open(temporary, "w", encoding="utf-8", newline="\n") as handle:
                handle.write(text)
                handle.write("\n")
            os.chmod(temporary, stat.S_IRUSR | stat.S_IWUSR)
            os.replace(temporary, self._state_path)
            os.chmod(self._state_path, stat.S_IRUSR | stat.S_IWUSR)

    def _save_lease(self, lease: Dict[str, Any]) -> None:
        """新增或更新单个租约，确保创建结果在进入浏览器流程前已持久化。"""
        lease_id = str(lease.get("lease_id", "") or "")
        if not lease_id:
            raise ICloudHMEError("iCloud HME 租约缺少 lease_id")
        with self._lock:
            payload = self._load_store()
            payload["leases"][lease_id] = dict(lease)
            self._write_store(payload)

    def _get_lease(self, lease_id: str) -> Optional[Dict[str, Any]]:
        """按令牌读取租约副本，避免调用方直接修改内存存储。"""
        if not lease_id:
            return None
        payload = self._load_store()
        lease = payload.get("leases", {}).get(lease_id)
        return dict(lease) if isinstance(lease, dict) else None

    def _log(self, message: str) -> None:
        """将提供商状态发送到主程序日志；无回调时保持安静。"""
        callback = self._log_callback
        if callback:
            try:
                callback(str(message))
            except Exception:
                pass


# 全局提供商实例在 GUI、CLI 和多 worker 间共享账号轮询游标与隧道进程。
_PROVIDER = ICloudHMEProvider()


def configure(
    config: Dict[str, Any],
    state_path: str,
    log_callback: Optional[Callable[[str], None]] = None,
) -> None:
    """配置全局 iCloud HME provider。"""
    _PROVIDER.configure(config, state_path, log_callback)


def check_connectivity(
    config: Dict[str, Any],
    state_path: str,
    log_callback: Optional[Callable[[str], None]] = None,
) -> Dict[str, int]:
    """建立或复用隧道并检查账号 API。"""
    configure(config, state_path, log_callback)
    return _PROVIDER.check_connectivity()


def create_mailbox(
    config: Dict[str, Any],
    state_path: str,
    log_callback: Optional[Callable[[str], None]] = None,
) -> Tuple[str, str]:
    """使用全局 provider 创建 iCloud 隐私邮箱。"""
    configure(config, state_path, log_callback)
    return _PROVIDER.create_mailbox()


def wait_for_code(
    config: Dict[str, Any],
    state_path: str,
    lease_token: str,
    email: str,
    *,
    timeout: int = 180,
    poll_interval: int = 3,
    raise_if_cancelled: Callable[[Optional[Callable[[], bool]]], None],
    sleep_with_cancel: Callable[[float, Optional[Callable[[], bool]]], None],
    log_callback: Optional[Callable[[str], None]] = None,
    cancel_callback: Optional[Callable[[], bool]] = None,
    resend_callback: Optional[Callable[[], None]] = None,
) -> str:
    """使用全局 provider 轮询指定隐私邮箱的验证码。"""
    configure(config, state_path, log_callback)
    return _PROVIDER.wait_for_code(
        lease_token,
        email,
        timeout=timeout,
        poll_interval=poll_interval,
        raise_if_cancelled=raise_if_cancelled,
        sleep_with_cancel=sleep_with_cancel,
        log_callback=log_callback,
        cancel_callback=cancel_callback,
        resend_callback=resend_callback,
    )


def retain_current_alias(
    config: Dict[str, Any],
    state_path: str,
    log_callback: Optional[Callable[[str], None]] = None,
) -> bool:
    """结束当前 worker 的租约占用，并永久保留对应 iCloud 隐私邮箱。"""
    configure(config, state_path, log_callback)
    return _PROVIDER.retain_current_alias(log_callback)


def shutdown() -> None:
    """关闭全局 provider 启动的 SSH 隧道，不删除任何隐私邮箱。"""
    _PROVIDER.shutdown()


# 进程正常退出时仅回收当前进程创建的 SSH 隧道。
atexit.register(shutdown)

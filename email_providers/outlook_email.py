"""OutlookEmail 完整 API 邮箱提供商。

本模块使用 Web 登录密码建立 Session，并通过 CSRF 保护的项目 API 领取、
结算邮箱；收信阶段使用同一 Session 调用内部邮件接口。登录密码仅保存在
调用方内存配置中，不会写入租约令牌、日志或邮箱凭证文件。
"""

from __future__ import annotations

import datetime as _datetime
import os
import threading
import time
import uuid
from email.utils import parsedate_to_datetime
from typing import Any, Callable, Dict, List, Optional, Tuple
from urllib.parse import quote, urlparse

import requests

from email_providers.common import extract_verification_code


# 默认项目标识保证所有 Grok worker 共享同一套邮箱消费状态。
DEFAULT_PROJECT_KEY = "grok-register"
# 默认项目名称用于 OutlookEmail 管理端展示业务用途。
DEFAULT_PROJECT_NAME = "Grok 注册"
# 单次 API 请求超时兼顾远端 Graph/IMAP 读取所需时间。
DEFAULT_REQUEST_TIMEOUT = 30
# 项目租约采用服务端允许的最大时长，覆盖一次完整注册和 OAuth 流程。
DEFAULT_LEASE_SECONDS = 3600
# 邮件时间容差用于兼容 Outlook、IMAP 与本机时钟之间的小幅偏差。
MESSAGE_TIME_GRACE_SECONDS = 120
# 支持的租约结算动作与 OutlookEmail 项目 API 路径一一对应。
CLAIM_OUTCOMES = {"success", "failed", "release"}


class OutlookEmailError(RuntimeError):
    """表示 OutlookEmail 登录、项目管理或邮件读取调用失败。"""


class OutlookEmailPoolEmptyError(OutlookEmailError):
    """表示当前项目没有可领取邮箱，调用方应停止本批任务。"""


def _normalize_group_ids(value: Any) -> List[int]:
    """把列表或逗号文本转换为去重后的正整数分组 ID。"""
    if value in (None, "", []):
        return []
    items = value if isinstance(value, (list, tuple, set)) else str(value).split(",")
    normalized: List[int] = []
    for item in items:
        text = str(item or "").strip()
        if not text:
            continue
        try:
            group_id = int(text)
        except (TypeError, ValueError) as exc:
            raise OutlookEmailError(f"OutlookEmail 分组 ID 无效: {text}") from exc
        if group_id <= 0:
            raise OutlookEmailError(f"OutlookEmail 分组 ID 必须为正整数: {text}")
        if group_id not in normalized:
            normalized.append(group_id)
    return normalized


def _parse_message_timestamp(value: Any) -> Optional[float]:
    """解析 Graph ISO 时间或 IMAP RFC 时间，无法识别时返回空值。"""
    text = str(value or "").strip()
    if not text:
        return None
    try:
        normalized = text[:-1] + "+00:00" if text.endswith("Z") else text
        parsed = _datetime.datetime.fromisoformat(normalized)
        if parsed.tzinfo is None:
            parsed = parsed.replace(tzinfo=_datetime.timezone.utc)
        return parsed.timestamp()
    except (TypeError, ValueError):
        pass
    try:
        parsed = parsedate_to_datetime(text)
        if parsed.tzinfo is None:
            parsed = parsed.replace(tzinfo=_datetime.timezone.utc)
        return parsed.timestamp()
    except (TypeError, ValueError, OverflowError):
        return None


def _message_fingerprint(message: Dict[str, Any]) -> str:
    """为缺少稳定 ID 的邮件生成可用于基线去重的指纹。"""
    return str(
        message.get("id")
        or "|".join(
            str(message.get(key, "") or "")
            for key in ("subject", "from", "date", "body_preview")
        )
    )


def _may_contain_verification_code(message: Dict[str, Any]) -> bool:
    """判断邮件元数据是否值得继续请求正文，减少无关详情调用。"""
    text = "\n".join(
        str(message.get(key, "") or "")
        for key in ("subject", "from", "body_preview")
    ).casefold()
    return any(
        keyword in text
        for keyword in (
            "xai",
            "x.ai",
            "verify",
            "verification",
            "security code",
            "验证码",
        )
    )


class OutlookEmailProvider:
    """管理 OutlookEmail 登录会话、项目邮箱租约和验证码轮询。"""

    def __init__(
        self,
        session_factory: Optional[Callable[[], requests.Session]] = None,
    ) -> None:
        """初始化线程隔离的 HTTP 会话和进程内非敏感租约索引。"""
        # 会话工厂允许测试注入假服务，并为每个 worker 创建独立 Cookie 容器。
        self._session_factory = session_factory or requests.Session
        # 线程局部状态隔离 Cookie、CSRF Token 和当前邮箱租约。
        self._thread_state = threading.local()
        # 可重入锁保护配置快照、项目启动缓存和跨线程租约字典。
        self._lock = threading.RLock()
        # 项目启动锁避免并发 worker 同时执行创建或补全范围操作。
        self._project_lock = threading.Lock()
        # 当前规范化配置仅在内存中保存，包含 Web 登录密码。
        self._config: Dict[str, Any] = {}
        # 配置指纹用于在地址或密码变化后废弃旧 Session。
        self._config_fingerprint = ""
        # 已启动项目缓存减少同一批次中的重复写请求。
        self._started_projects: set[Tuple[str, str]] = set()
        # 租约字典只保存服务端领取信息，不保存 Web 登录密码。
        self._leases: Dict[str, Dict[str, Any]] = {}
        # 调用方标识区分不同注册机进程，同时避免使用邮箱或主机名等敏感信息。
        self._caller_id = f"grok-register-{os.getpid()}-{uuid.uuid4().hex[:8]}"
        # 日志回调由 GUI 或 CLI 注入，并统一接受脱敏文本。
        self._log_callback: Optional[Callable[[str], None]] = None

    def configure(
        self,
        config: Dict[str, Any],
        log_callback: Optional[Callable[[str], None]] = None,
    ) -> None:
        """规范化完整 API 配置；密码只进入当前进程内存。"""
        raw_base = str(config.get("outlook_email_base_url", "") or "").strip()
        base_url = raw_base.rstrip("/")
        parsed = urlparse(base_url)
        if not base_url or parsed.scheme not in {"http", "https"} or not parsed.netloc:
            raise OutlookEmailError("请配置有效的 OutlookEmail 服务地址（http/https）")
        password = str(config.get("outlook_email_login_password", "") or "")
        if not password:
            raise OutlookEmailError("请配置 OutlookEmail Web 登录密码")
        project_key = str(
            config.get("outlook_email_project_key", DEFAULT_PROJECT_KEY)
            or DEFAULT_PROJECT_KEY
        ).strip().lower()
        if not project_key:
            raise OutlookEmailError("OutlookEmail 项目标识不能为空")
        normalized = {
            "base_url": base_url,
            "password": password,
            "project_key": project_key,
            "project_name": str(
                config.get("outlook_email_project_name", DEFAULT_PROJECT_NAME)
                or DEFAULT_PROJECT_NAME
            ).strip(),
            "group_ids": _normalize_group_ids(
                config.get("outlook_email_group_ids", [])
            ),
            "use_alias_email": bool(
                config.get("outlook_email_use_alias_email", False)
            ),
            "request_timeout": max(
                int(
                    config.get(
                        "outlook_email_request_timeout", DEFAULT_REQUEST_TIMEOUT
                    )
                    or DEFAULT_REQUEST_TIMEOUT
                ),
                1,
            ),
            "lease_seconds": min(
                max(
                    int(
                        config.get(
                            "outlook_email_lease_seconds", DEFAULT_LEASE_SECONDS
                        )
                        or DEFAULT_LEASE_SECONDS
                    ),
                    60,
                ),
                3600,
            ),
        }
        fingerprint = "|".join(
            (
                normalized["base_url"],
                normalized["password"],
                normalized["project_key"],
                ",".join(str(item) for item in normalized["group_ids"]),
                "1" if normalized["use_alias_email"] else "0",
            )
        )
        with self._lock:
            if self._config_fingerprint and self._config_fingerprint != fingerprint:
                self._started_projects.clear()
            self._config = normalized
            self._config_fingerprint = fingerprint
            if log_callback is not None:
                self._log_callback = log_callback

    def check_connectivity(self) -> Dict[str, Any]:
        """验证密码登录和内部 API，并返回邮箱池与项目摘要。"""
        self._ensure_configured()
        accounts_payload = self._request_json(
            "GET", "/api/accounts", params={"limit": 10000, "offset": 0}
        )
        projects_payload = self._request_json("GET", "/api/projects")
        accounts = accounts_payload.get("accounts") or []
        projects = (projects_payload.get("data") or {}).get("projects") or []
        project_key = self._project_key()
        project = next(
            (
                item
                for item in projects
                if isinstance(item, dict)
                and str(item.get("project_key", "") or "").strip().lower()
                == project_key
            ),
            None,
        )
        total = int(accounts_payload.get("total", len(accounts)) or 0)
        active = sum(
            1
            for item in accounts
            if isinstance(item, dict)
            and str(item.get("status", "active") or "active").lower() == "active"
        )
        return {
            "accounts": total,
            "active": active,
            "project_exists": bool(project),
            "to_claim": int((project or {}).get("to_claim_count", 0) or 0),
        }

    def create_mailbox(self) -> Tuple[str, str]:
        """创建或复用项目，并从项目邮箱池领取一个独占邮箱。"""
        self._ensure_configured()
        self._finalize_current_before_reuse()
        self._start_project()
        task_id = f"task-{uuid.uuid4().hex}"
        payload = self._request_json(
            "POST",
            f"/api/projects/{quote(self._project_key(), safe='')}/claim-random",
            json_body={
                "caller_id": self._caller_id,
                "task_id": task_id,
                "lease_seconds": int(self._config["lease_seconds"]),
            },
        )
        if payload.get("success") is not True:
            message = str(payload.get("error", "") or "没有可领取的项目邮箱")
            if "没有可领取" in message:
                raise OutlookEmailPoolEmptyError(message)
            raise OutlookEmailError(f"OutlookEmail 领取邮箱失败: {message}")
        data = payload.get("data") or {}
        email = str(data.get("email", "") or "").strip().lower()
        claim_token = str(data.get("claim_token", "") or "").strip()
        account_id = data.get("account_id")
        if not email or "@" not in email or not claim_token or not account_id:
            raise OutlookEmailError("OutlookEmail 领取响应缺少邮箱或租约字段")

        lease_token = f"outlook-email-{uuid.uuid4().hex}"
        lease = {
            "lease_token": lease_token,
            "project_key": self._project_key(),
            "account_id": int(account_id),
            "email": email,
            "claim_token": claim_token,
            "caller_id": self._caller_id,
            "task_id": task_id,
            "claimed_at_epoch": time.time(),
            "baseline_ids": [],
            "pending_outcome": "",
            "pending_detail": "",
        }
        try:
            lease["baseline_ids"] = sorted(self._snapshot_message_ids(email))
        except Exception as exc:
            self._log(f"[Debug] OutlookEmail 邮件基线读取失败，将改用时间过滤: {exc}")
        with self._lock:
            self._leases[lease_token] = lease
        self._thread_state.current_lease_token = lease_token
        self._log(f"[*] OutlookEmail 已从项目领取邮箱: {email}")
        return email, lease_token

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
        """轮询收件箱与垃圾邮件，并从新邮件主题、预览或正文提取验证码。"""
        self._ensure_configured()
        if log_callback is not None:
            self._log_callback = log_callback
        lease = self._get_lease(str(lease_token or ""))
        if not lease:
            raise OutlookEmailError("OutlookEmail 邮箱租约不存在或已结算")
        expected_email = str(lease.get("email", "") or "").strip().lower()
        if expected_email != str(email or "").strip().lower():
            raise OutlookEmailError("OutlookEmail 邮箱与领取租约不匹配")

        deadline = time.time() + max(int(timeout), 1)
        seen_ids = set(lease.get("baseline_ids") or [])
        claimed_at = float(lease.get("claimed_at_epoch", 0) or 0)
        next_resend_at = time.time() + 35
        last_error = ""
        while time.time() < deadline:
            raise_if_cancelled(cancel_callback)
            if resend_callback and time.time() >= next_resend_at:
                try:
                    resend_callback()
                    self._log("[*] 已触发重新发送 OutlookEmail 验证码")
                except Exception as exc:
                    self._log(f"[Debug] 触发重发 OutlookEmail 验证码失败: {exc}")
                next_resend_at = time.time() + 35
            try:
                messages = self._list_messages(email, top=20)
                for message in messages:
                    if not isinstance(message, dict):
                        continue
                    fingerprint = _message_fingerprint(message)
                    if not fingerprint or fingerprint in seen_ids:
                        continue
                    received_at = _parse_message_timestamp(message.get("date"))
                    if (
                        received_at is not None
                        and claimed_at
                        and received_at < claimed_at - MESSAGE_TIME_GRACE_SECONDS
                    ):
                        seen_ids.add(fingerprint)
                        continue
                    subject = str(message.get("subject", "") or "")
                    combined = "\n".join(
                        str(message.get(key, "") or "")
                        for key in ("body_preview", "from", "to")
                    )
                    code = extract_verification_code(combined, subject)
                    if code:
                        self._log(f"[*] OutlookEmail 从邮件列表提取到验证码: {code}")
                        return code
                    if not _may_contain_verification_code(message):
                        seen_ids.add(fingerprint)
                        continue
                    try:
                        detail = self._get_message_detail(email, message)
                    except Exception as exc:
                        # 详情读取可能暂时失败，不标记已读，下一轮仍会重试同一封邮件。
                        last_error = str(exc)
                        self._log(f"[Debug] OutlookEmail 邮件详情读取失败: {exc}")
                        continue
                    detail_subject = str(detail.get("subject", "") or subject)
                    detail_text = "\n".join(
                        str(detail.get(key, "") or "")
                        for key in ("body", "from", "to", "cc")
                    )
                    code = extract_verification_code(detail_text, detail_subject)
                    if code:
                        self._log(f"[*] OutlookEmail 从邮件正文提取到验证码: {code}")
                        return code
                    seen_ids.add(fingerprint)
                last_error = ""
            except Exception as exc:
                last_error = str(exc)
                self._log(f"[Debug] OutlookEmail 拉取邮件失败: {exc}")
            sleep_with_cancel(max(float(poll_interval), 0.2), cancel_callback)

        detail = f"，最后错误: {last_error}" if last_error else ""
        raise OutlookEmailError(
            f"OutlookEmail 在 {timeout}s 内未收到验证码邮件{detail}"
        )

    def finalize_current_claim(
        self,
        outcome: str,
        detail: str = "",
        log_callback: Optional[Callable[[str], None]] = None,
    ) -> bool:
        """按注册结果完成、失败或释放当前线程领取的邮箱。"""
        normalized_outcome = str(outcome or "").strip().lower()
        if normalized_outcome not in CLAIM_OUTCOMES:
            raise OutlookEmailError(f"不支持的 OutlookEmail 租约结算动作: {outcome}")
        if log_callback is not None:
            self._log_callback = log_callback
        lease_token = str(
            getattr(self._thread_state, "current_lease_token", "") or ""
        )
        if not lease_token:
            return True
        with self._lock:
            lease = self._leases.get(lease_token)
            if not lease:
                self._thread_state.current_lease_token = ""
                return True
            lease["pending_outcome"] = normalized_outcome
            lease["pending_detail"] = str(detail or "")[:500]
        self._finalize_lease(lease_token)
        return True

    def _start_project(self) -> Dict[str, Any]:
        """幂等创建或补全当前项目，确保新增邮箱进入领取范围。"""
        cache_key = (self._config_fingerprint, self._project_key())
        with self._project_lock:
            if cache_key in self._started_projects:
                return {}
            # 空 group_ids 也必须显式发送，才能把已有分组项目切换回全部邮箱范围。
            request_body: Dict[str, Any] = {
                "project_key": self._project_key(),
                "name": str(self._config.get("project_name", DEFAULT_PROJECT_NAME)),
                "description": "由 grok-register 自动管理的邮箱领取项目",
                "group_ids": list(self._config.get("group_ids") or []),
                "use_alias_email": bool(self._config.get("use_alias_email", False)),
            }
            payload = self._request_json(
                "POST", "/api/projects/start", json_body=request_body
            )
            if payload.get("success") is not True:
                raise OutlookEmailError(
                    f"OutlookEmail 启动项目失败: {payload.get('error') or '未知错误'}"
                )
            self._started_projects.add(cache_key)
            data = payload.get("data") or {}
            self._log(
                "[*] OutlookEmail 项目已就绪: "
                f"{self._project_key()}，新增邮箱={int(data.get('added_count', 0) or 0)}"
            )
            return data

    def _snapshot_message_ids(self, email: str) -> set[str]:
        """在提交注册邮箱前记录现有邮件，避免误取历史验证码。"""
        return {
            fingerprint
            for fingerprint in (
                _message_fingerprint(message)
                for message in self._list_messages(email, top=50)
                if isinstance(message, dict)
            )
            if fingerprint
        }

    def _list_messages(self, email: str, top: int) -> List[Dict[str, Any]]:
        """通过完整 API 同时读取收件箱和垃圾邮件的最新邮件。"""
        payload = self._request_json(
            "GET",
            f"/api/emails/{quote(str(email), safe='')}",
            params={"folder": "all", "skip": 0, "top": min(max(int(top), 1), 50)},
        )
        if payload.get("success") is not True:
            raise OutlookEmailError(
                f"OutlookEmail 读取邮件失败: {payload.get('error') or '未知错误'}"
            )
        messages = payload.get("emails") or []
        if not isinstance(messages, list):
            raise OutlookEmailError("OutlookEmail 邮件列表格式无效")
        return [item for item in messages if isinstance(item, dict)]

    def _get_message_detail(
        self,
        email: str,
        message: Dict[str, Any],
    ) -> Dict[str, Any]:
        """按列表返回的文件夹和 ID 模式读取单封邮件正文。"""
        message_id = str(message.get("id", "") or "").strip()
        if not message_id:
            raise OutlookEmailError("OutlookEmail 邮件详情缺少 message_id")
        id_mode = str(message.get("id_mode", "graph") or "graph").strip().lower()
        method = "graph" if id_mode == "graph" else "imap"
        payload = self._request_json(
            "GET",
            f"/api/email/{quote(str(email), safe='')}/{quote(message_id, safe='')}",
            params={
                "folder": str(message.get("folder", "inbox") or "inbox"),
                "method": method,
                "id_mode": id_mode,
            },
        )
        if payload.get("success") is not True:
            raise OutlookEmailError(
                f"OutlookEmail 邮件详情失败: {payload.get('error') or '未知错误'}"
            )
        detail = payload.get("email") or {}
        if not isinstance(detail, dict):
            raise OutlookEmailError("OutlookEmail 邮件详情格式无效")
        return detail

    def _finalize_current_before_reuse(self) -> None:
        """领取新邮箱前重试上次结算；无明确结果时安全释放旧租约。"""
        lease_token = str(
            getattr(self._thread_state, "current_lease_token", "") or ""
        )
        if not lease_token:
            return
        with self._lock:
            lease = self._leases.get(lease_token)
            if not lease:
                self._thread_state.current_lease_token = ""
                return
            if not lease.get("pending_outcome"):
                lease["pending_outcome"] = "release"
                lease["pending_detail"] = "领取新邮箱前释放未结算租约"
        self._finalize_lease(lease_token)

    def _finalize_lease(self, lease_token: str) -> None:
        """调用项目结算端点；请求失败时保留本地租约供下一轮重试。"""
        lease = self._get_lease(lease_token)
        if not lease:
            return
        outcome = str(lease.get("pending_outcome", "release") or "release")
        endpoint_name = {
            "success": "complete-success",
            "failed": "complete-failed",
            "release": "release",
        }[outcome]
        payload = self._request_json(
            "POST",
            "/api/projects/"
            f"{quote(str(lease['project_key']), safe='')}/{endpoint_name}",
            json_body={
                "account_id": int(lease["account_id"]),
                "claim_token": str(lease["claim_token"]),
                "caller_id": str(lease["caller_id"]),
                "task_id": str(lease["task_id"]),
                "detail": str(lease.get("pending_detail", "") or "")[:500],
            },
        )
        if payload.get("success") is not True:
            raise OutlookEmailError(
                f"OutlookEmail 租约结算失败: {payload.get('error') or '未知错误'}"
            )
        email = str(lease.get("email", "") or "")
        with self._lock:
            self._leases.pop(lease_token, None)
        if (
            str(getattr(self._thread_state, "current_lease_token", "") or "")
            == lease_token
        ):
            self._thread_state.current_lease_token = ""
        action_text = {"success": "标记成功", "failed": "标记失败", "release": "释放"}[
            outcome
        ]
        self._log(f"[*] OutlookEmail 已{action_text}项目邮箱: {email}")

    def _get_lease(self, lease_token: str) -> Optional[Dict[str, Any]]:
        """读取租约副本，避免网络调用期间持有全局锁。"""
        with self._lock:
            lease = self._leases.get(str(lease_token or ""))
            return dict(lease) if isinstance(lease, dict) else None

    def _http_state(self) -> Dict[str, Any]:
        """返回当前 worker 的 Session 与 CSRF 状态，配置变化时自动重建。"""
        state = getattr(self._thread_state, "http_state", None)
        if not isinstance(state, dict) or state.get("fingerprint") != self._config_fingerprint:
            session = self._session_factory()
            if hasattr(session, "trust_env"):
                session.trust_env = False
            state = {
                "fingerprint": self._config_fingerprint,
                "session": session,
                "authenticated": False,
                "csrf_token": "",
            }
            self._thread_state.http_state = state
        return state

    def _login(self, state: Dict[str, Any]) -> None:
        """使用 Web 登录密码建立 Session，并立即获取同会话 CSRF Token。"""
        session = state["session"]
        try:
            session.cookies.clear()
        except Exception:
            pass
        response = session.request(
            "POST",
            f"{self._api_base()}/login",
            json={"password": str(self._config["password"])},
            timeout=int(self._config["request_timeout"]),
        )
        payload = self._decode_response(response, "POST", "/login")
        if int(getattr(response, "status_code", 0) or 0) >= 400 or payload.get("success") is not True:
            state["authenticated"] = False
            raise OutlookEmailError(
                f"OutlookEmail 登录失败: {payload.get('error') or '密码或服务状态异常'}"
            )
        state["authenticated"] = True
        self._refresh_csrf(state)

    def _refresh_csrf(self, state: Dict[str, Any]) -> None:
        """刷新当前登录 Session 对应的 CSRF Token。"""
        response = state["session"].request(
            "GET",
            f"{self._api_base()}/api/csrf-token",
            timeout=int(self._config["request_timeout"]),
        )
        payload = self._decode_response(response, "GET", "/api/csrf-token")
        if int(getattr(response, "status_code", 0) or 0) >= 400:
            state["authenticated"] = False
            raise OutlookEmailError("OutlookEmail 获取 CSRF Token 失败")
        state["csrf_token"] = str(payload.get("csrf_token", "") or "")

    def _request_json(
        self,
        method: str,
        path: str,
        *,
        params: Optional[Dict[str, Any]] = None,
        json_body: Optional[Dict[str, Any]] = None,
    ) -> Dict[str, Any]:
        """调用完整 API，并在 Session 过期或 CSRF 失效时自动重登一次。"""
        normalized_method = str(method or "GET").upper()
        for attempt in range(2):
            state = self._http_state()
            if not state.get("authenticated"):
                self._login(state)
            headers = {"Accept": "application/json"}
            if normalized_method not in {"GET", "HEAD", "OPTIONS"} and state.get(
                "csrf_token"
            ):
                headers["X-CSRFToken"] = str(state["csrf_token"])
            response = state["session"].request(
                normalized_method,
                f"{self._api_base()}{path}",
                params=params,
                json=json_body,
                headers=headers,
                timeout=int(self._config["request_timeout"]),
            )
            payload = self._decode_response(response, normalized_method, path)
            status = int(getattr(response, "status_code", 0) or 0)
            needs_login = status == 401 or payload.get("need_login") is True
            csrf_error = status == 400 and payload.get("csrf_error") is True
            if attempt == 0 and (needs_login or csrf_error):
                state["authenticated"] = False
                state["csrf_token"] = ""
                continue
            if status >= 400:
                raise OutlookEmailError(
                    f"OutlookEmail API 失败 {normalized_method} {path}，"
                    f"HTTP {status}: {payload.get('error') or '未知错误'}"
                )
            return payload
        raise OutlookEmailError(f"OutlookEmail API 重试失败: {normalized_method} {path}")

    def _decode_response(
        self,
        response: Any,
        method: str,
        path: str,
    ) -> Dict[str, Any]:
        """解析 JSON 响应，并为反向代理错误页生成有限长度诊断信息。"""
        try:
            payload = response.json()
        except Exception as exc:
            preview = str(getattr(response, "text", "") or "")[:200]
            raise OutlookEmailError(
                f"OutlookEmail 返回非 JSON {method} {path}: {preview}"
            ) from exc
        if not isinstance(payload, dict):
            raise OutlookEmailError(
                f"OutlookEmail 响应格式无效 {method} {path}"
            )
        return payload

    def _api_base(self) -> str:
        """返回已经校验并移除尾部斜杠的服务地址。"""
        return str(self._config.get("base_url", "") or "").rstrip("/")

    def _project_key(self) -> str:
        """返回当前项目的规范化标识。"""
        return str(
            self._config.get("project_key", DEFAULT_PROJECT_KEY)
            or DEFAULT_PROJECT_KEY
        )

    def _ensure_configured(self) -> None:
        """确认调用方已经注入完整 API 地址和登录密码。"""
        if not self._config:
            raise OutlookEmailError("OutlookEmail provider 尚未配置")

    def _log(self, message: str) -> None:
        """向主程序发送状态日志，回调异常不得中断邮箱流程。"""
        callback = self._log_callback
        if callback:
            try:
                callback(str(message))
            except Exception:
                pass


# 全局实例让 GUI、CLI 和多 worker 共享项目启动缓存与租约索引。
_PROVIDER = OutlookEmailProvider()


def configure(
    config: Dict[str, Any],
    log_callback: Optional[Callable[[str], None]] = None,
) -> None:
    """配置全局 OutlookEmail 完整 API 客户端。"""
    _PROVIDER.configure(config, log_callback)


def check_connectivity(config: Dict[str, Any]) -> Dict[str, Any]:
    """验证全局客户端的密码登录和内部 API 可用性。"""
    configure(config)
    return _PROVIDER.check_connectivity()


def create_mailbox(
    config: Dict[str, Any],
    log_callback: Optional[Callable[[str], None]] = None,
) -> Tuple[str, str]:
    """从配置项目领取一个邮箱并返回非敏感本地租约令牌。"""
    configure(config, log_callback)
    return _PROVIDER.create_mailbox()


def wait_for_code(
    config: Dict[str, Any],
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
    """使用全局客户端轮询指定领取邮箱的 xAI 验证码。"""
    configure(config, log_callback)
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


def finalize_current_claim(
    config: Dict[str, Any],
    outcome: str,
    detail: str = "",
    log_callback: Optional[Callable[[str], None]] = None,
) -> bool:
    """结算当前线程领取的项目邮箱，失败时保留本地状态供重试。"""
    configure(config, log_callback)
    return _PROVIDER.finalize_current_claim(outcome, detail, log_callback)

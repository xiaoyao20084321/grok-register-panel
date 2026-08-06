#!/usr/bin/env python
# -*- coding: utf-8 -*-
"""
Grok 注册机 - TTK GUI 版本
整合 openai_register.py, batch_open_nsfw.py（原 DrissionPage 已替换为 Camoufox）
"""

import tkinter as tk
from tkinter import ttk, messagebox, scrolledtext
import threading
import datetime
import time
import os
from pathlib import Path
import sys
import signal
import gc
import queue
import secrets
import struct
import random
import re
import string
import json
import base64
import hashlib
import concurrent.futures
from urllib.parse import quote, urlsplit, urlunsplit

os.environ.setdefault("TK_SILENCE_DEPRECATION", "1")

from playwright._impl._errors import TargetClosedError as PageDisconnectedError
from curl_cffi import CurlMime, requests
import requests as _std_requests

# SSO → CLIProxyAPI(CPA) 扁平格式转换（复用 sso_to_auth_json 的授权码流程 + 写入器）
import sso_to_auth_json as _s2cpa
from email_providers import cloudflare as cloudflare_provider
from email_providers import cloudmail as cloudmail_provider
from email_providers import duckmail as duckmail_provider
from email_providers import icloud_hme as icloud_hme_provider
from email_providers import mailnest as mailnest_provider
from email_providers import outlook_email as outlook_email_provider
from email_providers import yyds as yyds_provider
from email_providers.common import extract_verification_code as _extract_code
from email_providers.common import generate_username as _generate_username
from email_providers.common import pick_list_payload as _pick_list

import browser_session as _bs
import register_flow as _rf
import connectivity as _conn
import resin_tunnel as _resin_tunnel
from browser_session import (

    browser,
    page,
    active_browser as _active_browser,
    active_page as _active_page,
    set_browser_session as _set_browser_session,
    start_browser,
    stop_browser,
    restart_browser,
    cleanup_runtime_memory,
    refresh_active_page,
    extract_cf_clearance_and_ua,
    create_browser_options,
    get_start_fail_streak,
    cleanup_stale_profiles as _cleanup_stale_profiles,
    get_exit_ip,
    get_bound_proxy,
    clear_exit_context,
)
from register_flow import (
    SIGNUP_URL,
    authorize_device_in_browser,
    click_email_signup_button,
    open_signup_page,
    has_profile_form,
    detect_email_domain_rejection,
    raise_if_email_domain_rejected,
    fill_email_and_submit,
    fill_code_and_submit,
    getTurnstileToken,
    build_profile,
    fill_profile_and_submit,
    login_grok_with_email_password,
    wait_for_sso_cookie,
)



APP_DIR = os.path.dirname(os.path.abspath(__file__))
CONFIG_FILE = os.path.join(APP_DIR, "config.json")
# 注册产物目录（账号 / 邮箱凭证 / 待重转 SSO），避免堆在项目根目录
ACCOUNTS_DIR = os.path.join(APP_DIR, "accounts")
MEMORY_CLEANUP_INTERVAL = 5
# 待恢复 SSO 队列文件保存已建号但尚未取得 Cookie 的邮箱与 Grok 密码。
SSO_RECOVERY_FILE_NAME = "sso_recovery_pending.jsonl"

_session_log_path = None
_session_log_lock = threading.Lock()
# 待恢复队列锁保护多 worker 的原子读取、更新和任务领取。
_SSO_RECOVERY_LOCK = threading.RLock()
# 当前进程正在恢复的邮箱集合用于避免并发 worker 重复登录同一账号。
_SSO_RECOVERY_ACTIVE_EMAILS = set()
# 当前批次已经尝试过的邮箱集合保证每个待恢复账号每轮最多执行一次。
_SSO_RECOVERY_ATTEMPTED_EMAILS = set()
# 当前批次启动时的队列快照避免本轮新产生的 SSO 超时账号被立即再次登录。
_SSO_RECOVERY_ELIGIBLE_EMAILS = set()


def ensure_accounts_dir():
    """确保 accounts/ 存在，返回目录绝对路径。"""
    os.makedirs(ACCOUNTS_DIR, exist_ok=True)
    return ACCOUNTS_DIR


def new_accounts_output_path(now=None):
    """本批次账号输出路径：accounts/accounts_YYYYMMDD_HHMMSS.txt

    仅作为批次汇总文件（兼容旧逻辑）；每个账号还会单独保存到 accounts/{email}.txt。
    """
    ensure_accounts_dir()
    ts = (now or datetime.datetime.now()).strftime("%Y%m%d_%H%M%S")
    return os.path.join(ACCOUNTS_DIR, f"accounts_{ts}.txt")


def account_file_for_email(email):
    """单个账号的独立输出路径：accounts/{email}.txt"""
    ensure_accounts_dir()
    safe_email = str(email or "").strip().replace("/", "_").replace("\\", "_")
    return os.path.join(ACCOUNTS_DIR, f"{safe_email}.txt")


def accounts_side_file(name):
    """accounts/ 下的附属文件路径（mail_credentials / sso_pending 等）。"""
    ensure_accounts_dir()
    return os.path.join(ACCOUNTS_DIR, name)


def sso_recovery_file_path():
    """返回待恢复 SSO 队列文件路径，并确保账号目录已经创建。"""
    return accounts_side_file(SSO_RECOVERY_FILE_NAME)


def get_sso_recovery_count():
    """返回当前磁盘队列中的有效待恢复账号数量，不读取或暴露密码内容。"""
    with _SSO_RECOVERY_LOCK:
        return len(_load_sso_recovery_records_unlocked())


def _load_sso_recovery_records_unlocked():
    """在调用方持锁时读取并按邮箱去重待恢复记录，损坏行会被安全跳过。"""
    path = sso_recovery_file_path()
    if not os.path.exists(path):
        return []
    records_by_email = {}
    try:
        with open(path, "r", encoding="utf-8") as recovery_file:
            for raw_line in recovery_file:
                line = raw_line.strip()
                if not line:
                    continue
                try:
                    record = json.loads(line)
                except (TypeError, ValueError, json.JSONDecodeError):
                    continue
                if not isinstance(record, dict):
                    continue
                email = str(record.get("email", "") or "").strip().lower()
                password = str(record.get("password", "") or "")
                if not email or "@" not in email or not password:
                    continue
                normalized = dict(record)
                normalized["email"] = email
                normalized["password"] = password
                records_by_email[email] = normalized
    except OSError:
        return []
    return list(records_by_email.values())


def _write_sso_recovery_records_unlocked(records):
    """在调用方持锁时原子重写待恢复队列，并把敏感文件权限限制为 0600。"""
    path = sso_recovery_file_path()
    temporary_path = f"{path}.tmp-{os.getpid()}-{threading.get_ident()}"
    try:
        with open(temporary_path, "w", encoding="utf-8", newline="\n") as recovery_file:
            for record in records:
                recovery_file.write(json.dumps(record, ensure_ascii=False) + "\n")
            recovery_file.flush()
            os.fsync(recovery_file.fileno())
        try:
            os.chmod(temporary_path, 0o600)
        except OSError:
            pass
        os.replace(temporary_path, path)
        try:
            os.chmod(path, 0o600)
        except OSError:
            pass
    finally:
        if os.path.exists(temporary_path):
            try:
                os.remove(temporary_path)
            except OSError:
                pass


def prepare_sso_recovery_run():
    """在独立恢复任务开始时冻结队列快照，使每个账号本轮最多尝试一次。"""
    with _SSO_RECOVERY_LOCK:
        _SSO_RECOVERY_ACTIVE_EMAILS.clear()
        _SSO_RECOVERY_ATTEMPTED_EMAILS.clear()
        _SSO_RECOVERY_ELIGIBLE_EMAILS.clear()
        _SSO_RECOVERY_ELIGIBLE_EMAILS.update(
            str(record.get("email", "") or "").strip().lower()
            for record in _load_sso_recovery_records_unlocked()
            if str(record.get("email", "") or "").strip()
        )


def queue_sso_recovery(email, password, detail="", log_callback=None):
    """保存已建号但缺少 SSO 的登录凭据；重复邮箱只更新状态而不重复写入。"""
    normalized_email = str(email or "").strip().lower()
    normalized_password = str(password or "")
    if not normalized_email or "@" not in normalized_email or not normalized_password:
        raise ValueError("待恢复 SSO 记录缺少邮箱或 Grok 密码")
    now = datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    with _SSO_RECOVERY_LOCK:
        records = _load_sso_recovery_records_unlocked()
        existing = next(
            (item for item in records if item.get("email") == normalized_email),
            None,
        )
        if existing is None:
            existing = {
                "email": normalized_email,
                "password": normalized_password,
                "created_at": now,
                "updated_at": now,
                "attempts": 0,
                "last_error": str(detail or "")[:500],
            }
            records.append(existing)
        else:
            existing["password"] = normalized_password
            existing["updated_at"] = now
            if detail:
                existing["last_error"] = str(detail)[:500]
        _write_sso_recovery_records_unlocked(records)
    if log_callback:
        log_callback(f"[*] 已保存待恢复 SSO 账号: {normalized_email}")
    return True


def remove_sso_recovery(email, log_callback=None):
    """在取得 SSO 后从登录恢复队列删除指定邮箱，避免下次恢复任务重复登录。"""
    normalized_email = str(email or "").strip().lower()
    if not normalized_email:
        return False
    with _SSO_RECOVERY_LOCK:
        records = _load_sso_recovery_records_unlocked()
        remaining = [
            item for item in records if item.get("email") != normalized_email
        ]
        removed = len(remaining) != len(records)
        if removed:
            _write_sso_recovery_records_unlocked(remaining)
        _SSO_RECOVERY_ACTIVE_EMAILS.discard(normalized_email)
    if removed and log_callback:
        log_callback(f"[*] 已完成 SSO 恢复并移出队列: {normalized_email}")
    return removed


def claim_next_sso_recovery():
    """为当前 worker 领取本批次尚未尝试的待恢复账号，队列为空时返回空值。"""
    with _SSO_RECOVERY_LOCK:
        for record in _load_sso_recovery_records_unlocked():
            email = str(record.get("email", "") or "").strip().lower()
            if (
                not email
                or email not in _SSO_RECOVERY_ELIGIBLE_EMAILS
                or email in _SSO_RECOVERY_ACTIVE_EMAILS
                or email in _SSO_RECOVERY_ATTEMPTED_EMAILS
            ):
                continue
            _SSO_RECOVERY_ACTIVE_EMAILS.add(email)
            _SSO_RECOVERY_ATTEMPTED_EMAILS.add(email)
            return dict(record)
    return None


def finish_sso_recovery_attempt(email, error=""):
    """结束一次恢复领取；失败时累计次数并保留记录供下次独立任务再次尝试。"""
    normalized_email = str(email or "").strip().lower()
    now = datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    with _SSO_RECOVERY_LOCK:
        records = _load_sso_recovery_records_unlocked()
        changed = False
        for record in records:
            if record.get("email") != normalized_email:
                continue
            record["attempts"] = int(record.get("attempts", 0) or 0) + 1
            record["updated_at"] = now
            record["last_error"] = redact_sensitive_text(error)[:500]
            changed = True
            break
        if changed:
            _write_sso_recovery_records_unlocked(records)
        _SSO_RECOVERY_ACTIVE_EMAILS.discard(normalized_email)
    return changed


def initialize_session_log(log_dir=None, now=None):
    """为本次程序启动创建一个独立的 UTF-8 日志文件。"""
    global _session_log_path
    with _session_log_lock:
        if _session_log_path:
            return _session_log_path

        target_dir = log_dir or os.path.join(APP_DIR, "log")
        os.makedirs(target_dir, exist_ok=True)
        timestamp = (now or datetime.datetime.now()).strftime("%Y%m%d_%H%M%S")
        suffix = 1
        while True:
            suffix_text = "" if suffix == 1 else f"_{suffix}"
            path = os.path.join(target_dir, f"app_{timestamp}{suffix_text}.log")
            try:
                with open(path, "x", encoding="utf-8", newline="\n"):
                    pass
            except FileExistsError:
                suffix += 1
                continue
            _session_log_path = path
            return path


def append_session_log(line):
    path = _session_log_path
    if not path:
        return
    try:
        with _session_log_lock:
            with open(path, "a", encoding="utf-8", newline="\n") as log_file:
                log_file.write(f"{line}\n")
    except OSError:
        # 持久化日志失败不应中断正在进行的注册任务。
        pass

# 主窗口使用浅灰背景，避免 macOS 原生控件与深色文字发生反差。
UI_BG = "#f4f5f7"
# 配置面板使用白色背景，突出分组边界并保持内容清晰。
UI_PANEL_BG = "#ffffff"
# 所有主要文本使用深灰色，确保浅色控件上的可读性。
UI_FG = "#1f2937"
# 次要文本使用中灰色，用于禁用控件和辅助状态信息。
UI_MUTED_FG = "#6b7280"
# 输入框和下拉菜单使用白色底色，与 macOS 原生控件保持一致。
UI_ENTRY_BG = "#ffffff"
# 普通按钮使用浅灰底色，避免与面板白色背景完全融为一体。
UI_BUTTON_BG = "#e5e7eb"
# 鼠标悬停和选择状态使用浅蓝色，保留明确的交互反馈。
UI_ACTIVE_BG = "#dbeafe"

# DEFAULT_CONFIG 汇总所有 provider、代理、注册流程和输出目录的默认配置。
DEFAULT_CONFIG = {
    "email_provider": "cloudflare",
    # iCloud HME API 仅通过本机 SSH 隧道访问，禁止配置公网服务地址。
    "icloud_api_base": "http://127.0.0.1:18090",
    # 开启后由注册机自动复用或建立 SSH 本地端口转发。
    "icloud_enable_tunnel": True,
    # SSH 私钥只用于本地启动隧道，App 专用密码不会进入本配置。
    "icloud_ssh_key": "~/.ssh/MaXiangLinTxCloudMiYao.pem",
    # SSH 登录用户与云服务器系统账号保持一致。
    "icloud_ssh_user": "ubuntu",
    # SSH 主机必须由 config.json 显式配置，示例文件提供当前部署地址。
    "icloud_ssh_host": "",
    # 本地监听端口必须与 icloud_api_base 中的端口一致。
    "icloud_local_port": 18090,
    # 远端端口对应服务器回环地址上的 icloud-hme 服务。
    "icloud_remote_port": 8090,
    # 单次 icloud-hme API 请求超时，单位为秒。
    "icloud_request_timeout": 30,
    # SSH 隧道启动后等待 API 就绪的最长时间，单位为秒。
    "icloud_tunnel_timeout": 15,
    # OutlookEmail 完整 API 地址可以是 HTTPS 反向代理或受保护的内网地址。
    "outlook_email_base_url": "",
    # Web 登录密码只写入被 Git 忽略的 config.json，并用于建立 Session。
    "outlook_email_login_password": "",
    # 项目标识保证所有 Grok worker 共享同一套邮箱领取状态。
    "outlook_email_project_key": "grok-register",
    # 项目名称仅用于 OutlookEmail 管理端展示。
    "outlook_email_project_name": "Grok 注册",
    # 分组 ID 留空表示使用全部普通邮箱；填写后只补入指定分组及其子分组。
    "outlook_email_group_ids": [],
    # 开启后项目优先领取账号别名，未配置别名的账号仍回退主邮箱。
    "outlook_email_use_alias_email": False,
    # 完整 API 请求超时需要覆盖远端 Graph/IMAP 读取。
    "outlook_email_request_timeout": 30,
    # 项目租约使用服务端允许的最大一小时，覆盖完整注册流程。
    "outlook_email_lease_seconds": 3600,
    "duckmail_api_key": "",
    "duckmail_api_base": "https://api.duckmail.sbs",
    "defaultDomains": "",
    "cloudmail_url": "",
    "cloudmail_admin_email": "",
    "cloudmail_password": "",
    "cloudflare_api_base": "",
    "cloudflare_api_key": "",
    "cloudflare_auth_mode": "none",
    "cloudflare_custom_auth": "",
    "cloudflare_path_domains": "/api/domains",
    "cloudflare_path_accounts": "/api/new_address",
    "cloudflare_path_token": "/api/token",
    "cloudflare_path_messages": "/api/mails",
    # 代理模式默认保持原有普通代理行为；resin 表示按账号启用粘性身份。
    "proxy_mode": "normal",
    "proxy": "http://127.0.0.1:7890",
    # Resin 正向代理密码只保存在被 Git 忽略的 config.json 中。
    "resin_token": "",
    # Resin 默认平台包含全部已导入节点，可在 GUI 中切换到自定义平台。
    "resin_platform": "Default",
    # Resin 自动隧道默认关闭；已有 iCloud SSH 主机的旧配置会在加载时自动启用。
    "resin_enable_tunnel": False,
    # Resin SSH 私钥与 iCloud 可使用相同文件，但配置项保持相互独立。
    "resin_ssh_key": "~/.ssh/MaXiangLinTxCloudMiYao.pem",
    # Resin SSH 用户对应部署服务的云服务器系统账号。
    "resin_ssh_user": "ubuntu",
    # Resin SSH 主机默认留空，旧配置首次加载时可从 iCloud 主机迁移。
    "resin_ssh_host": "",
    # Resin 本地端口是程序实际连接的 SSH 转发入口。
    "resin_local_port": 12260,
    # Resin 远端端口对应云服务器回环地址上的 Resin 服务。
    "resin_remote_port": 2260,
    # Resin 隧道超时覆盖 SSH 握手和 `/healthz` 首次响应。
    "resin_tunnel_timeout": 15,
    "debug_mode": False,
    "close_browser_on_stop": False,
    "log_level": "info",
    "register_count": 1,
    "register_workers": 1,
    "user_agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/138.0.0.0 Safari/537.36",
    # CLIProxyAPI(CPA) 直出：注册拿到 SSO 后换 token，写入 CPA / Grok2API
    "cpa_auto_add": False,
    # CPA 输出默认开启；关闭后既不上传 CPA，也不生成 CPA 本地备用文件。
    "cpa_enabled": True,
    # Grok2API 输出默认开启；关闭后不处理 Grok Web 和 Grok Build。
    "grok2api_enabled": True,
    # Token 换取方式：device_protocol（协议 Device Flow，默认）/ device_browser（浏览器 Device Flow）/ auth_code
    "cpa_token_mode": "device_protocol",
    # CPA 远程不可用时才写入此本地备用目录。
    "cpa_auth_dir": "cpa_auth",
    # 远程 CPA：通过 Management API POST /v0/management/auth-files 上传
    "cpa_remote_url": "",
    "cpa_management_key": "",
    # Grok2API 远程不可用时，把 Web/Build 导入文件写入此本地备用目录。
    "grok2api_auth_dir": "grok2api_auth",
    # Grok2API 管理后台基础地址；程序会自行拼接登录和账号导入路径。
    "grok2api_remote_url": "",
    # Grok2API 管理员用户名用于换取短期 Bearer Token。
    "grok2api_admin_username": "",
    # Grok2API 管理员密码只保存在被 Git 忽略的 config.json 中。
    "grok2api_admin_password": "",
    "mailnest_api_key": "",
    "mailnest_project_code": "x-ai001",
    # YYDS：留空自动选已验证域名；填写则固定该域名
    "yyds_default_domain": "",
    # 账号间注册间隔（秒），0=不等待。填一个整数=N秒固定等待，填区间"60-120"=随机等待
    "account_interval": "60-120",
}

config = DEFAULT_CONFIG.copy()
_cf_domain_index = 0


class RegistrationCancelled(Exception):
    pass


class AccountRetryNeeded(Exception):
    pass


class EmailDomainRejected(Exception):
    """xAI 拒绝当前邮箱域名（如公共临时域被拉黑）。"""

    def __init__(self, email="", message=""):
        self.email = email or ""
        self.message = message or "邮箱域名已被拒绝"
        domain = ""
        if "@" in self.email:
            domain = self.email.split("@", 1)[1]
        detail = self.message
        if domain and domain not in detail:
            detail = f"{detail}（域名: {domain}）"
        if self.email and self.email not in detail:
            detail = f"{detail} | 邮箱: {self.email}"
        super().__init__(detail)


class RegistrationRiskDenied(Exception):
    """账号已创建，但服务端将本次注册裁决为 OAuth 不可用。"""



FAIL_DOMAIN = "domain_rejected"
FAIL_RISK = "registration_risk"
FAIL_CODE = "code_timeout"
FAIL_BROWSER = "browser"
FAIL_CPA = "cpa"
FAIL_STUCK = "stuck_retry"
FAIL_SSO = "sso_timeout"
FAIL_TURNSTILE = "turnstile"
FAIL_PROFILE = "profile_fill"
# FAIL_ICLOUD_LIMIT 单独统计 Apple 隐藏邮箱创建额度，避免归入模糊的“其它”。
FAIL_ICLOUD_LIMIT = "icloud_hme_limit"
# FAIL_OUTLOOK_POOL 单独统计项目邮箱耗尽，便于整批自动停止。
FAIL_OUTLOOK_POOL = "outlook_email_pool_empty"
FAIL_OTHER = "other"


def redact_proxy(url: str) -> str:
    """Strip credentials from proxy URL for logs/jsonl."""
    s = str(url or "").strip()
    if not s:
        return ""
    try:
        from urllib.parse import urlparse, urlunparse
        if "://" not in s:
            parts = s.split(":")
            if len(parts) >= 4:
                return f"{parts[0]}:{parts[1]}:***"
            return s
        p = urlparse(s)
        if p.username or p.password:
            host = p.hostname or ""
            netloc = f"{host}:{p.port}" if p.port else host
            return urlunparse((p.scheme, netloc, p.path, p.params, p.query, p.fragment))
        return s
    except Exception:
        import re as _re
        return _re.sub(r"://([^:/@]+):([^@/]+)@", r"://***:***@", s)


def redact_sensitive_text(message) -> str:
    """遮蔽日志中的代理、邮箱和输出服务密钥，兼容 URL 编码形态。"""
    text = str(message)
    secrets_to_mask = (
        str(config.get("resin_token", "") or ""),
        str(config.get("cpa_management_key", "") or ""),
        str(config.get("grok2api_admin_password", "") or ""),
        str(config.get("outlook_email_login_password", "") or ""),
    )
    for secret in secrets_to_mask:
        for secret_value in (secret, quote(secret, safe="")):
            if secret_value:
                text = text.replace(secret_value, "***")
    return text


def mask_email(email: str) -> str:
    s = str(email or "").strip()
    if "@" not in s:
        return s
    local, _, domain = s.partition("@")
    if len(local) <= 2:
        return (local[:1] + "***@" + domain) if local else ("***@" + domain)
    return local[:2] + "***@" + domain


# FAIL_LABELS 把内部失败分类转换为 GUI、CLI 共用的中文统计标签。
FAIL_LABELS = {
    FAIL_DOMAIN: "域名拒绝",
    FAIL_RISK: "注册风控",
    FAIL_CODE: "验证码超时",
    FAIL_BROWSER: "浏览器断开",
    FAIL_CPA: "CPA失败",
    FAIL_STUCK: "流程卡住",
    FAIL_SSO: "SSO超时",
    FAIL_TURNSTILE: "资料页Turnstile",
    FAIL_PROFILE: "资料填写",
    FAIL_ICLOUD_LIMIT: "iCloud额度",
    FAIL_OUTLOOK_POOL: "Outlook邮箱池耗尽",
    FAIL_OTHER: "其它",
}



_RESULT_LOG_LOCK = threading.Lock()
_RESULT_LOG_PATH = os.path.join(
    os.path.dirname(os.path.abspath(__file__)), "log", "register_results.jsonl"
)


def record_register_result(
    status: str,
    email: str = "",
    *,
    kind: str = "",
    detail: str = "",
    worker: str = "",
    bot_flag=None,
    risk=None,
    log_callback=None,
) -> dict:
    """记录单次注册结果 + 出口 IP（控制台一行 + jsonl）。

    status: ok / fail / risk / sso_timeout / browser / other
    """
    import json as _json
    from datetime import datetime, timezone

    exit_ip = ""
    proxy = ""
    try:
        exit_ip = get_exit_ip() or ""
    except Exception:
        pass
    try:
        proxy = get_bound_proxy() or ""
    except Exception:
        pass
    # 从 proxy URL 抽端口
    port = ""
    try:
        if "://" in proxy:
            hostport = proxy.split("://", 1)[1]
            if ":" in hostport:
                port = hostport.rsplit(":", 1)[-1]
    except Exception:
        pass

    rec = {
        "ts": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "status": status,
        "email": mask_email(email or ""),
        "kind": kind or "",
        "detail": redact_sensitive_text(detail or "")[:300],
        "worker": worker or "",
        "exit_ip": exit_ip,
        "proxy": redact_proxy(proxy),
        "port": port,
        "resin_account": get_thread_resin_account(),
        "bot_flag": bot_flag,
        "risk": risk,
    }
    line = (
        f"[结果] status={status} ip={exit_ip or '?'} port={port or '?'} "
        f"email={email or '-'} kind={kind or '-'} bot={bot_flag if bot_flag is not None else '-'} "
        f"risk={risk if risk is not None else '-'} "
        f"resin={get_thread_resin_account() or '-'}"
    )
    if log_callback:
        try:
            log_callback(line)
        except Exception:
            pass
    try:
        os.makedirs(os.path.dirname(_RESULT_LOG_PATH), exist_ok=True)
        with _RESULT_LOG_LOCK:
            with open(_RESULT_LOG_PATH, "a", encoding="utf-8") as f:
                f.write(_json.dumps(rec, ensure_ascii=False) + "\n")
    except Exception as exc:
        if log_callback:
            try:
                log_callback(f"[结果] 写入 jsonl 失败: {exc}")
            except Exception:
                pass
    return rec


def classify_failure(exc) -> str:
    """把注册异常归入稳定分类，供统计、日志和批次终止策略使用。"""
    if isinstance(exc, icloud_hme_provider.ICloudHMEAddressLimitError):
        return FAIL_ICLOUD_LIMIT
    if isinstance(exc, outlook_email_provider.OutlookEmailPoolEmptyError):
        return FAIL_OUTLOOK_POOL
    if isinstance(exc, EmailDomainRejected):
        return FAIL_DOMAIN
    if isinstance(exc, RegistrationRiskDenied):
        return FAIL_RISK
    msg = str(exc or "")
    low = msg.lower()
    if isinstance(exc, AccountRetryNeeded) or "达到最大重试" in msg or "流程卡住" in msg:
        return FAIL_STUCK
    if "sso_timeout" in low or "未获取到 sso" in msg or "未获取到 sso cookie" in msg:
        return FAIL_SSO
    if (
        "资料页 Turnstile" in msg
        or "Turnstile 超时" in msg
        or "Turnstile 获取 token 失败" in msg
        or ("turnstile" in low and ("超时" in msg or "失败" in msg or "token" in low))
    ):
        return FAIL_TURNSTILE
    if (
        "资料页表单未就绪" in msg
        or "资料页无提交按钮" in msg
        or "资料页输入写入失败" in msg
        or "资料页提交后未进入登录重定向阶段" in msg
        or "最终注册页资料填写失败" in msg
    ):
        return FAIL_PROFILE
    if "未收到验证码" in msg or "验证码阶段失败" in msg or ("验证码" in msg and "失败" in msg):
        return FAIL_CODE
    if (
        "浏览器" in msg
        or "page disconnected" in low
        or "与页面的连接已断开" in msg
        or "PageDisconnected" in msg
        or "disconnected" in low
    ):
        return FAIL_BROWSER
    if "[CPA]" in msg or ("CPA" in msg and ("失败" in msg or "跳过" in msg)):
        return FAIL_CPA
    return FAIL_OTHER


def empty_fail_stats():
    return {k: 0 for k in FAIL_LABELS}


def format_fail_stats(stats: dict) -> str:
    parts = [f"{FAIL_LABELS.get(k, k)}={stats.get(k, 0)}" for k in FAIL_LABELS if stats.get(k, 0)]
    if not parts:
        return "无分类失败"
    return " | ".join(parts)



def load_config():
    """加载用户配置，并为首次出现的 Resin 隧道字段迁移 iCloud SSH 参数。"""
    global config
    if os.path.exists(CONFIG_FILE):
        try:
            with open(CONFIG_FILE, "r", encoding="utf-8") as f:
                loaded = json.load(f)
            config = {**DEFAULT_CONFIG, **loaded}
            # 旧配置没有 Resin SSH 字段时，优先沿用用户已经确认可用的 iCloud
            # 服务器、账号和私钥；写回 config.json 后两组字段仍可独立修改。
            resin_ssh_fallbacks = {
                "resin_ssh_key": "icloud_ssh_key",
                "resin_ssh_user": "icloud_ssh_user",
                "resin_ssh_host": "icloud_ssh_host",
            }
            for resin_key, icloud_key in resin_ssh_fallbacks.items():
                if resin_key not in loaded and str(loaded.get(icloud_key, "") or ""):
                    config[resin_key] = loaded[icloud_key]
            if "resin_enable_tunnel" not in loaded:
                config["resin_enable_tunnel"] = bool(
                    str(config.get("resin_ssh_host", "") or "").strip()
                )

            # 用户原来直连本机 Resin 的 2260 端口时，首次启用自动隧道自动迁移
            # 到 12260；其他自定义代理地址保持原样，避免覆盖用户选择。
            if (
                "resin" in str(config.get("proxy_mode", "") or "").lower()
                and bool(config.get("resin_enable_tunnel"))
                and "resin_local_port" not in loaded
            ):
                try:
                    parsed_proxy = urlsplit(str(config.get("proxy", "") or ""))
                    if (
                        parsed_proxy.hostname
                        in ("127.0.0.1", "localhost", "::1")
                        and parsed_proxy.port
                        == int(config.get("resin_remote_port", 2260) or 2260)
                    ):
                        config["proxy"] = (
                            "http://127.0.0.1:"
                            f"{int(config.get('resin_local_port', 12260) or 12260)}"
                        )
                except (TypeError, ValueError):
                    pass
        except Exception:
            config = DEFAULT_CONFIG.copy()
    return config


def parse_account_interval() -> float:
    """解析 account_interval 配置，返回等待秒数。

    "0" / "" → 0（不等待）
    "30" → 30.0（固定 30 秒）
    "60-120" → 60~120 之间的随机值
    """
    raw = str(config.get("account_interval", "0") or "0").strip()
    if not raw or raw == "0":
        return 0.0
    if "-" in raw:
        parts = raw.split("-", 1)
        try:
            lo = max(int(parts[0].strip()), 0)
            hi = max(int(parts[1].strip()), lo)
            return float(random.randint(lo, hi))
        except (ValueError, IndexError):
            return 0.0
    try:
        return float(int(raw))
    except ValueError:
        return 0.0


def save_config():
    """保存包含认证信息的本地配置，并在类 Unix 系统限制为仅当前用户可读写。"""
    try:
        with open(CONFIG_FILE, "w", encoding="utf-8") as f:
            json.dump(config, f, indent=4, ensure_ascii=False)
        # Web 登录密码和各输出密钥都在此文件中，类 Unix 保存后立即收紧权限。
        if os.name != "nt":
            os.chmod(CONFIG_FILE, 0o600)
    except Exception as e:
        print(f"保存配置失败: {e}")


def ensure_stable_python_runtime():
    if sys.version_info < (3, 14) or os.environ.get("DPE_REEXEC_DONE") == "1":
        return

    local_app_data = os.environ.get("LOCALAPPDATA", "")
    candidates = [
        os.path.join(local_app_data, "Programs", "Python", "Python312", "python.exe"),
        os.path.join(local_app_data, "Programs", "Python", "Python313", "python.exe"),
    ]

    current_python = os.path.normcase(os.path.abspath(sys.executable))
    for candidate in candidates:
        if not os.path.isfile(candidate):
            continue
        if os.path.normcase(os.path.abspath(candidate)) == current_python:
            return

        print(
            f"[*] 检测到 Python {sys.version.split()[0]}，自动切换到更稳定的解释器: {candidate}"
        )
        env = os.environ.copy()
        env["DPE_REEXEC_DONE"] = "1"
        os.execve(candidate, [candidate, os.path.abspath(__file__), *sys.argv[1:]], env)


def warn_runtime_compatibility():
    if sys.version_info >= (3, 14):
        print(
            "[提示] 当前 Python 为 3.14+；若出现 Mail.tm TLS 异常，建议改用 Python 3.12 或 3.13。"
        )


ensure_stable_python_runtime()
warn_runtime_compatibility()

load_config()

# turnstilePatch 是 Chrome 扩展，Camoufox 基于 Firefox 不兼容，已移除。
# Turnstile 交互改为纯 JS 注入方式（见 register_flow.getTurnstileToken）。
EXTENSION_PATH = ""


DUCKMAIL_API_BASE_DEFAULT = duckmail_provider.API_BASE_DEFAULT


# PROXY_MODE_NORMAL 表示直接使用用户填写的普通代理地址。
PROXY_MODE_NORMAL = "normal"
# PROXY_MODE_RESIN 表示使用 Resin V1 的 Platform.Account 粘性身份。
PROXY_MODE_RESIN = "resin"
# RESIN_DEFAULT_PLATFORM 对应 Resin 自动创建并包含全部节点的默认平台。
RESIN_DEFAULT_PLATFORM = "Default"
# RESIN_FORBIDDEN_IDENTITY_CHARS 与 Resin V1 对 Token、Platform 的限制保持一致。
RESIN_FORBIDDEN_IDENTITY_CHARS = frozenset(".:|/\\@?#%~ \t\n\r")
# RESIN_RESERVED_PROXY_TOKENS 对齐 Resin 服务启动时拒绝的路由保留字。
RESIN_RESERVED_PROXY_TOKENS = frozenset(("api", "healthz", "ui"))
# RESIN_RESERVED_PLATFORM_NAMES 对齐 Resin 平台名称校验中的保留字。
RESIN_RESERVED_PLATFORM_NAMES = frozenset(("api",))
# XAI_STARTUP_CHECK_ATTEMPTS 表示启动前连续失败三次才终止注册批次。
XAI_STARTUP_CHECK_ATTEMPTS = 3

# 每个 worker 在线程本地保存当前账号的代理与 Resin 租约身份。
_proxy_tls = threading.local()
# _proxy_pool 保存普通代理模式下从 proxies.txt 读取的代理列表。
_proxy_pool: list = []
# _proxy_pool_lock 保护普通代理池的重新加载，避免并发启动时读到半成品列表。
_proxy_pool_lock = threading.Lock()


def get_proxy_mode(source_config: dict | None = None) -> str:
    """返回规范化代理模式；旧配置或未知值一律回落为普通代理。"""
    source = config if source_config is None else source_config
    raw = str(source.get("proxy_mode", PROXY_MODE_NORMAL) or PROXY_MODE_NORMAL)
    normalized = raw.strip().lower()
    if normalized in (
        PROXY_MODE_RESIN,
        "resin_sticky",
        "resin 粘性代理",
        "resin粘性代理",
    ):
        return PROXY_MODE_RESIN
    return PROXY_MODE_NORMAL


def is_resin_proxy_mode(source_config: dict | None = None) -> bool:
    """判断当前配置是否启用 Resin 粘性代理。"""
    return get_proxy_mode(source_config) == PROXY_MODE_RESIN


def normalize_resin_tunnel_proxy(source_config: dict) -> str:
    """迁移 Resin 自动隧道的旧本机入口，并返回最终代理地址。

    仅当代理为空，或仍指向与远端端口相同的本机旧入口时，才改为配置的本地
    转发端口；其他自定义地址保持不变，后续校验会提示端口是否匹配。
    """
    current = str(source_config.get("proxy", "") or "").strip()
    if (
        not is_resin_proxy_mode(source_config)
        or not bool(source_config.get("resin_enable_tunnel", False))
    ):
        return current
    try:
        local_port = int(source_config.get("resin_local_port", 12260) or 12260)
        remote_port = int(source_config.get("resin_remote_port", 2260) or 2260)
        parsed = urlsplit(current) if current else None
        should_migrate = not current or (
            parsed is not None
            and parsed.hostname in ("127.0.0.1", "localhost", "::1")
            and parsed.port == remote_port
            and local_port != remote_port
        )
    except (TypeError, ValueError):
        return current
    if should_migrate:
        current = f"http://127.0.0.1:{local_port}"
        source_config["proxy"] = current
    return current


def validate_resin_proxy_settings(
    proxy_url: str,
    token: str,
    platform: str,
) -> None:
    """校验 Resin 地址和 V1 身份字段，失败时抛出可直接展示给用户的异常。"""
    raw_proxy = str(proxy_url or "").strip()
    raw_token = str(token or "")
    raw_platform = str(platform or "").strip()
    if not raw_proxy:
        raise ValueError("Resin 粘性代理需要填写代理地址")
    try:
        parsed = urlsplit(raw_proxy)
        parsed_port = parsed.port
    except ValueError as exc:
        raise ValueError(f"Resin 代理地址无效: {exc}") from exc
    if parsed.scheme.lower() not in ("http", "socks5", "socks5h"):
        raise ValueError("Resin 代理地址仅支持 http://、socks5:// 或 socks5h://")
    if not parsed.hostname:
        raise ValueError("Resin 代理地址缺少主机名")
    if parsed_port is not None and not (1 <= parsed_port <= 65535):
        raise ValueError("Resin 代理端口必须在 1-65535 之间")
    if parsed.username is not None or parsed.password is not None:
        raise ValueError("Resin 代理地址不要包含认证信息，请单独填写 Token 和 Platform")
    if parsed.path not in ("", "/") or parsed.query or parsed.fragment:
        raise ValueError("Resin 代理地址只能填写到主机和端口，不能包含路径或查询参数")
    if not raw_token:
        raise ValueError("Resin 粘性代理需要填写 Resin Token")
    if any(char in RESIN_FORBIDDEN_IDENTITY_CHARS for char in raw_token):
        raise ValueError("Resin Token 含有 V1 不允许的符号或空白字符")
    if raw_token in RESIN_RESERVED_PROXY_TOKENS:
        raise ValueError("Resin Token 不能使用 api、healthz 或 ui 保留字")
    if not raw_platform:
        raise ValueError("Resin 粘性代理需要填写 Platform")
    if any(char in RESIN_FORBIDDEN_IDENTITY_CHARS for char in raw_platform):
        raise ValueError("Resin Platform 含有 V1 不允许的符号或空白字符")
    if raw_platform.casefold() in RESIN_RESERVED_PLATFORM_NAMES:
        raise ValueError("Resin Platform 不能使用 api 保留字")


def validate_proxy_config(source_config: dict | None = None) -> None:
    """校验当前代理及可选 Resin SSH 隧道；普通代理保持宽松兼容。"""
    source = config if source_config is None else source_config
    if not is_resin_proxy_mode(source):
        return
    normalize_resin_tunnel_proxy(source)
    validate_resin_proxy_settings(
        str(source.get("proxy", "") or ""),
        str(source.get("resin_token", "") or ""),
        str(source.get("resin_platform", RESIN_DEFAULT_PLATFORM) or ""),
    )
    _resin_tunnel.validate_config(source)


def build_resin_proxy_url(
    proxy_url: str,
    token: str,
    platform: str,
    account: str,
) -> str:
    """构造 Resin V1 正向代理 URL，并对认证字段进行安全的 URL 编码。"""
    validate_resin_proxy_settings(proxy_url, token, platform)
    raw_account = str(account or "").strip()
    if not raw_account:
        raise ValueError("Resin 粘性代理缺少当前账号标识")
    if any(char in RESIN_FORBIDDEN_IDENTITY_CHARS for char in raw_account):
        raise ValueError("Resin Account 含有 V1 不允许的符号或空白字符")

    parsed = urlsplit(str(proxy_url).strip())
    hostname = str(parsed.hostname or "")
    # IPv6 主机在重新组装 netloc 时必须恢复方括号，否则端口会被误解析。
    host_text = f"[{hostname}]" if ":" in hostname else hostname
    if parsed.port is not None:
        host_text = f"{host_text}:{parsed.port}"
    identity = quote(f"{str(platform).strip()}.{raw_account}", safe="")
    encoded_token = quote(str(token), safe="")
    return urlunsplit(
        (
            parsed.scheme.lower(),
            f"{identity}:{encoded_token}@{host_text}",
            "",
            "",
            "",
        )
    )


def new_resin_batch_id(now: datetime.datetime | None = None) -> str:
    """生成本轮注册批次标识，避免不同程序实例复用同一 Resin 租约。"""
    current = now or datetime.datetime.now()
    return f"{current.strftime('%Y%m%d%H%M%S')}_{secrets.token_hex(3)}"


def resin_account_id(
    batch_id: str,
    worker_id: int,
    account_index: int,
    generation: int = 0,
) -> str:
    """生成 Resin Account；同一账号槽位保持稳定，显式换租约时追加代次。"""
    safe_batch = re.sub(r"[^A-Za-z0-9_-]+", "_", str(batch_id or "")).strip("_")
    if not safe_batch:
        safe_batch = new_resin_batch_id()
    account = (
        f"grok_{safe_batch}_w{max(int(worker_id), 0) + 1}"
        f"_n{max(int(account_index), 0) + 1}"
    )
    if generation > 0:
        account += f"_r{int(generation)}"
    return account


def load_proxy_pool(path: str = "") -> list:
    """加载普通代理池；Resin 模式只使用 GUI 中填写的统一入口地址。"""
    global _proxy_pool
    with _proxy_pool_lock:
        if is_resin_proxy_mode():
            single = str(config.get("proxy", "") or "").strip()
            _proxy_pool = [single] if single else []
            return list(_proxy_pool)

        candidates = []
        if path:
            candidates.append(Path(path))
        candidates.append(Path(APP_DIR) / "proxies.txt")
        pool = []
        for fp in candidates:
            try:
                if not fp.is_file():
                    continue
                for line in fp.read_text(encoding="utf-8").splitlines():
                    candidate = line.strip()
                    if not candidate or candidate.startswith("#"):
                        continue
                    if candidate.startswith(
                        ("http://", "socks5://", "socks5h://")
                    ):
                        pool.append(candidate)
                if pool:
                    break
            except Exception:
                continue
        if not pool:
            single = str(config.get("proxy", "") or "").strip()
            if single:
                pool = [single]
        _proxy_pool = pool
        return list(_proxy_pool)


def set_thread_proxy(proxy: str):
    """把当前注册 worker 的完整代理 URL 绑定到线程上下文。"""
    _proxy_tls.proxy = str(proxy or "").strip()


def get_thread_proxy() -> str:
    """返回当前注册 worker 已绑定的代理 URL。"""
    return str(getattr(_proxy_tls, "proxy", "") or "").strip()


def pick_proxy_for_worker(worker_id: int, rotate_idx: int = 0) -> str:
    """为普通代理 worker 从其代理池分片中选择当前轮换项。"""
    pool = _proxy_pool or load_proxy_pool()
    if not pool:
        return str(config.get("proxy", "") or "").strip()
    # 按 worker 分片，再在分片内用 rotate_idx 轮换
    # 简化：全局 round-robin 用 wid + rotate_idx * max_workers 映射
    workers = max(1, int(config.get("register_workers", 1) or 1))
    # 该 worker 可用的下标: wid, wid+workers, wid+2*workers, ...
    indices = list(range(worker_id % len(pool), len(pool), workers))
    if not indices:
        indices = [worker_id % len(pool)]
    idx = indices[rotate_idx % len(indices)]
    return pool[idx]


def bind_proxy_for_account(
    batch_id: str,
    worker_id: int,
    account_index: int,
    *,
    rotate_idx: int = 0,
    force_new_resin_lease: bool = False,
    resin_generation: int | None = None,
) -> tuple[str, str]:
    """为一个注册账号绑定代理，返回完整代理 URL 与 Resin Account。

    Resin 模式用批次、worker 和账号序号形成稳定槽位；当前槽位发生浏览器或
    邮箱重试时复用相同 Account。只有在尚未开始注册且明确要求跳过坏出口时，
    ``force_new_resin_lease`` 才会增加代次并申请新租约。启动预检成功后可通过
    ``resin_generation`` 把对应代次交给首个注册 worker 继续复用。自动 SSH
    隧道若在批次运行期间断开，会在下一次账号绑定时重新建立。
    """
    if not is_resin_proxy_mode():
        proxy = pick_proxy_for_worker(worker_id, rotate_idx)
        set_thread_proxy(proxy)
        _proxy_tls.resin_slot = ""
        _proxy_tls.resin_generation = 0
        _proxy_tls.resin_account = ""
        return proxy, ""

    validate_proxy_config()
    if bool(config.get("resin_enable_tunnel", False)):
        _resin_tunnel.ensure(config)
    slot = (
        f"{str(batch_id)}|{max(int(worker_id), 0)}|"
        f"{max(int(account_index), 0)}"
    )
    previous_slot = str(getattr(_proxy_tls, "resin_slot", "") or "")
    if previous_slot != slot:
        generation = max(int(resin_generation or 0), 0)
    else:
        generation = int(getattr(_proxy_tls, "resin_generation", 0) or 0)
        if resin_generation is not None:
            generation = max(int(resin_generation), 0)
        elif force_new_resin_lease:
            generation += 1
    account = resin_account_id(batch_id, worker_id, account_index, generation)
    proxy = build_resin_proxy_url(
        str(config.get("proxy", "") or ""),
        str(config.get("resin_token", "") or ""),
        str(config.get("resin_platform", RESIN_DEFAULT_PLATFORM) or ""),
        account,
    )
    _proxy_tls.resin_slot = slot
    _proxy_tls.resin_generation = generation
    _proxy_tls.resin_account = account
    set_thread_proxy(proxy)
    return proxy, account


def get_thread_resin_account() -> str:
    """返回当前 worker 的 Resin Account，普通代理模式返回空字符串。"""
    return str(getattr(_proxy_tls, "resin_account", "") or "")


def connectivity_config_for_proxy(
    source_config: dict | None = None,
    account: str = "",
) -> dict:
    """构造连通性检查专用配置，并在 Resin 模式下注入可认证的粘性代理 URL。"""
    source = config if source_config is None else source_config
    result = dict(source)
    if not is_resin_proxy_mode(source):
        return result
    validate_proxy_config(source)
    check_account = str(account or "").strip()
    if not check_account:
        check_account = resin_account_id(new_resin_batch_id(), 0, 0)
    result["proxy"] = build_resin_proxy_url(
        str(source.get("proxy", "") or ""),
        str(source.get("resin_token", "") or ""),
        str(source.get("resin_platform", RESIN_DEFAULT_PLATFORM) or ""),
        check_account,
    )
    return result


def get_proxies():
    """返回当前 worker 的 HTTP/HTTPS 代理映射，供浏览器外请求统一复用。"""
    proxy = get_thread_proxy() or str(config.get("proxy", "") or "").strip()
    if proxy:
        return {"http": proxy, "https": proxy}
    return {}


# _MAIL_DIRECT_MARKERS 标识不得经过住宅代理的本地或邮箱服务请求。
_MAIL_DIRECT_MARKERS = (
    "http://127.0.0.1:",
    "http://localhost:",
    "mail-api.example.com",
    "hermaly.com",
    "example.com",
    "/admin/new_address",
    "/api/mails",
    "/api/mail/",
)


def _url_needs_direct(url: str) -> bool:
    """判断请求是否必须绕过注册住宅代理直接访问。"""
    u = str(url or "").lower()
    return any(m in u for m in _MAIL_DIRECT_MARKERS)


def _apply_mail_direct(url, request_kwargs: dict) -> dict:
    """邮箱 Worker API 强制直连，避免经住宅代理 TLS 失败。"""
    if _url_needs_direct(url):
        rk = dict(request_kwargs)
        rk["proxies"] = {}
        return rk
    return request_kwargs


def get_duckmail_api_base():
    return duckmail_provider.normalize_base(str(config.get("duckmail_api_base", "") or ""))


def get_duckmail_api_key():
    return config.get("duckmail_api_key", "")



def get_cloudflare_api_base():
    return str(config.get("cloudflare_api_base", "") or "").rstrip("/")


def get_cloudflare_api_key():
    return config.get("cloudflare_api_key", "")


def get_cloudflare_auth_mode():
    return str(config.get("cloudflare_auth_mode", "none") or "none").lower()


def get_cloudflare_custom_auth():
    """全局访问密码（cloudflare_temp_email 的 PASSWORDS）。"""
    return str(config.get("cloudflare_custom_auth", "") or "").strip()


def cloudflare_apply_custom_auth(headers):
    return cloudflare_provider.apply_custom_auth(headers, get_cloudflare_custom_auth())


def get_cloudflare_path(key, default_path):
    return cloudflare_provider.path_from_config(config, key, default_path)


def cloudflare_build_headers(content_type=False):
    return cloudflare_provider.build_headers(
        get_cloudflare_api_key(),
        get_cloudflare_auth_mode(),
        get_cloudflare_custom_auth(),
        content_type=content_type,
    )


def cloudflare_apply_auth_params(params=None):
    return cloudflare_provider.apply_auth_params(
        params, get_cloudflare_api_key(), get_cloudflare_auth_mode()
    )


def cloudflare_next_default_domain():
    global _cf_domain_index
    domains = [x.strip() for x in str(config.get("defaultDomains", "") or "").split(",") if x.strip()]
    domain, _cf_domain_index = cloudflare_provider.next_default_domain(domains, _cf_domain_index)
    return domain


def cloudflare_is_admin_create_path(path):
    return cloudflare_provider.is_admin_create_path(path)


def _pick_list_payload(data):
    return _pick_list(data)


def cloudflare_create_temp_address(api_base):
    return cloudflare_provider.create_temp_address(
        http_post,
        api_base,
        accounts_path=get_cloudflare_path("cloudflare_path_accounts", "/api/new_address"),
        domain=cloudflare_next_default_domain(),
        api_key=get_cloudflare_api_key(),
        auth_mode=get_cloudflare_auth_mode(),
        custom_auth=get_cloudflare_custom_auth(),
        name=generate_username(10),
    )


MAILNEST_API_BASE = mailnest_provider.API_BASE
MAILNEST_DEFAULT_PROJECT_CODE = mailnest_provider.DEFAULT_PROJECT_CODE


def get_mailnest_api_key():
    key = str(config.get("mailnest_api_key", "") or "").strip()
    if not key:
        raise Exception(f"请在配置文件中配置 mailnest_api_key | 注册网址：{MAILNEST_API_BASE}")
    return key


def get_mailnest_project_code():
    code = str(config.get("mailnest_project_code", "") or "").strip()
    return code or MAILNEST_DEFAULT_PROJECT_CODE


def mailnest_buy_email():
    return mailnest_provider.buy_email(http_post, get_mailnest_api_key(), get_mailnest_project_code())


def mailnest_receive_email(email):
    return mailnest_provider.receive_email(http_post, get_mailnest_api_key(), email)


def mailnest_get_code(email, timeout=180, poll_interval=3, log_callback=None, cancel_callback=None):
    return mailnest_provider.wait_for_code(
        http_post,
        get_mailnest_api_key(),
        email,
        timeout=timeout,
        poll_interval=poll_interval,
        raise_if_cancelled=raise_if_cancelled,
        sleep_with_cancel=sleep_with_cancel,
        log_callback=log_callback,
        cancel_callback=cancel_callback,
    )


def get_user_agent():
    return config.get(
        "user_agent",
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/138.0.0.0 Safari/537.36",
    )


def _normalize_sso_token(raw_token):
    token = str(raw_token or "").strip()
    if token.startswith("sso="):
        token = token[4:]
    return token


def _resolve_cpa_proxy():
    """CPA 换 token 用的代理：优先线程绑定 / config.proxy，其次环境变量，否则直连。"""
    proxy = get_thread_proxy() or str(config.get("proxy", "") or "").strip()
    if proxy:
        return proxy
    for key in ("https_proxy", "HTTPS_PROXY", "http_proxy", "HTTP_PROXY"):
        val = str(os.environ.get(key, "") or "").strip()
        if val:
            return val
    return ""


# REMOTE_UPLOAD_RETRIES 表示首次失败后额外重试三次，合计最多四次请求。
REMOTE_UPLOAD_RETRIES = 3
# _grok2api_admin_token_cache 复用短期管理员 Token，避免每个账号重复登录触发限流。
_grok2api_admin_token_cache: dict = {}
# _grok2api_admin_token_lock 串行化管理员登录和缓存更新，兼容多 worker 注册。
_grok2api_admin_token_lock = threading.Lock()


def get_auth_output_selection(source_config: dict | None = None) -> tuple[bool, bool]:
    """返回 CPA 与 Grok2API 两个独立输出开关，旧配置默认全部开启。"""
    source = config if source_config is None else source_config
    return (
        bool(source.get("cpa_enabled", True)),
        bool(source.get("grok2api_enabled", True)),
    )


def has_selected_auth_output_target(source_config: dict | None = None) -> bool:
    """判断每个已勾选输出是否都配置了远程地址或本地备用目录。"""
    source = config if source_config is None else source_config
    cpa_enabled, grok2api_enabled = get_auth_output_selection(source)
    selected_targets = []
    if cpa_enabled:
        selected_targets.append(
            any(
                str(source.get(key, "") or "").strip()
                for key in ("cpa_remote_url", "cpa_auth_dir")
            )
        )
    if grok2api_enabled:
        selected_targets.append(
            any(
                str(source.get(key, "") or "").strip()
                for key in ("grok2api_remote_url", "grok2api_auth_dir")
            )
        )
    return bool(selected_targets) and all(selected_targets)


def _grok2api_admin_cache_key(
    base_url: str,
    username: str,
    password: str,
) -> tuple[str, str, str]:
    """生成不含明文密码的管理员 Token 缓存键。"""
    password_digest = hashlib.sha256(str(password).encode("utf-8")).hexdigest()
    return (
        str(base_url or "").strip().rstrip("/"),
        str(username or "").strip(),
        password_digest,
    )


def _grok2api_response_error(response, operation: str) -> RuntimeError:
    """把 Grok2API HTTP 错误转换成不泄露凭据的简短异常。"""
    body = str(getattr(response, "text", "") or "").replace("\n", " ").strip()
    if len(body) > 300:
        body = body[:300] + "..."
    status_code = int(getattr(response, "status_code", 0) or 0)
    return RuntimeError(
        f"{operation}失败 HTTP {status_code}: {body or 'empty response'}"
    )


def _parse_grok2api_expiry(value: str) -> float:
    """解析 Grok2API 管理员 Token 过期时间，异常时使用五分钟安全缓存。"""
    fallback = time.time() + 300
    raw = str(value or "").strip()
    if not raw:
        return fallback
    try:
        parsed = datetime.datetime.fromisoformat(raw.replace("Z", "+00:00"))
        return parsed.timestamp()
    except (TypeError, ValueError, OverflowError):
        return fallback


def _get_grok2api_admin_token(
    base_url: str,
    username: str,
    password: str,
) -> str:
    """登录 Grok2API 并缓存管理员 Bearer Token，供 Web/Build 导入共用。"""
    base = str(base_url or "").strip().rstrip("/")
    admin_username = str(username or "").strip()
    admin_password = str(password or "")
    if not base:
        raise ValueError("Grok2API 服务器地址为空")
    if not admin_username:
        raise ValueError("Grok2API 管理员用户名为空")
    if not admin_password:
        raise ValueError("Grok2API 管理员密码为空")

    cache_key = _grok2api_admin_cache_key(base, admin_username, admin_password)
    with _grok2api_admin_token_lock:
        cached = _grok2api_admin_token_cache.get(cache_key) or {}
        cached_token = str(cached.get("access_token") or "")
        cached_expiry = float(cached.get("expires_at") or 0)
        if cached_token and cached_expiry > time.time() + 60:
            return cached_token

        response = requests.post(
            f"{base}/api/admin/v1/auth/login",
            json={"username": admin_username, "password": admin_password},
            timeout=30,
            proxies={},
            impersonate="chrome",
        )
        if response.status_code >= 400:
            raise _grok2api_response_error(response, "Grok2API 管理员登录")
        try:
            payload = response.json()
            data = payload.get("data") if isinstance(payload, dict) else None
            tokens = data.get("tokens") if isinstance(data, dict) else None
            access_token = (
                str(tokens.get("accessToken") or "")
                if isinstance(tokens, dict)
                else ""
            )
            expires_at = (
                str(tokens.get("accessTokenExpiresAt") or "")
                if isinstance(tokens, dict)
                else ""
            )
        except Exception as exc:
            raise RuntimeError(f"Grok2API 登录响应解析失败: {exc}") from exc
        if not access_token:
            raise RuntimeError("Grok2API 登录响应缺少 accessToken")
        _grok2api_admin_token_cache[cache_key] = {
            "access_token": access_token,
            "expires_at": _parse_grok2api_expiry(expires_at),
        }
        return access_token


def _invalidate_grok2api_admin_token(
    base_url: str,
    username: str,
    password: str,
) -> None:
    """在服务端拒绝管理员 Token 后清除对应缓存，允许下一次重试重新登录。"""
    cache_key = _grok2api_admin_cache_key(base_url, username, password)
    with _grok2api_admin_token_lock:
        _grok2api_admin_token_cache.pop(cache_key, None)


def _parse_grok2api_import_stream(response, operation: str) -> dict:
    """解析 Grok2API SSE 导入结果，仅 complete 事件代表服务端真正接收成功。"""
    if response.status_code >= 400:
        raise _grok2api_response_error(response, operation)
    text = str(response.text or "")
    for block in re.split(r"\r?\n\r?\n", text):
        event_name = ""
        data_lines = []
        for line in block.splitlines():
            if line.startswith("event:"):
                event_name = line[6:].strip()
            elif line.startswith("data:"):
                data_lines.append(line[5:].strip())
        if not event_name:
            continue
        raw_data = "\n".join(data_lines).strip()
        try:
            event_data = json.loads(raw_data) if raw_data else {}
        except json.JSONDecodeError as exc:
            raise RuntimeError(f"{operation}返回了无效 SSE JSON") from exc
        if event_name == "error":
            message = (
                str(event_data.get("message") or event_data.get("code") or "")
                if isinstance(event_data, dict)
                else ""
            )
            raise RuntimeError(f"{operation}失败: {message or 'unknown error'}")
        if event_name == "complete":
            if not isinstance(event_data, dict):
                raise RuntimeError(f"{operation}完成事件格式无效")
            return event_data
    raise RuntimeError(f"{operation}未返回 complete 事件")


def _run_grok2api_web_account_tools_background(
    base_url: str,
    username: str,
    password: str,
    email: str,
) -> None:
    """后台定位刚导入的 Web 账号并执行协议、生日和 NSFW，忽略所有结果。"""
    base = str(base_url or "").strip().rstrip("/")
    target_email = str(email or "").strip()
    if not base or not target_email:
        return
    try:
        access_token = _get_grok2api_admin_token(base, username, password)
        headers = {"Authorization": f"Bearer {access_token}"}
        response = requests.get(
            f"{base}/api/admin/v1/accounts",
            headers=headers,
            params={
                "page": "1",
                "pageSize": "20",
                "provider": "grok_web",
                "search": target_email,
            },
            timeout=30,
            proxies={},
            impersonate="chrome",
        )
        if response.status_code == 401:
            _invalidate_grok2api_admin_token(base, username, password)
            return
        if response.status_code >= 400:
            return
        payload = response.json()
        data = payload.get("data") if isinstance(payload, dict) else None
        items = data.get("items") if isinstance(data, dict) else None
        if not isinstance(items, list):
            return
        account_id = ""
        for item in items:
            if not isinstance(item, dict):
                continue
            item_email = str(item.get("email") or "").strip()
            item_name = str(item.get("name") or "").strip()
            if target_email.casefold() not in {
                item_email.casefold(),
                item_name.casefold(),
            }:
                continue
            if str(item.get("provider") or "") != "grok_web":
                continue
            account_id = str(item.get("id") or "").strip()
            if account_id:
                break
        if not account_id:
            return
        response = requests.post(
            f"{base}/api/admin/v1/accounts/web/run-scripts",
            headers={
                **headers,
                "Accept": "text/event-stream",
            },
            json={
                "ids": [account_id],
                "actions": {
                    "acceptTerms": True,
                    "setBirthDate": True,
                    "enableNSFW": True,
                },
            },
            # 后台保持 SSE 连接，主注册流程不等待任务完成。
            timeout=600,
            proxies={},
            impersonate="chrome",
        )
        if response.status_code == 401:
            _invalidate_grok2api_admin_token(base, username, password)
    except Exception:
        # 账号工具属于尽力而为的后台附加动作，任何失败都不得影响注册结果。
        return


def _start_grok2api_web_account_tools_background(
    base_url: str,
    username: str,
    password: str,
    email: str,
) -> None:
    """启动守护线程执行 Grok2API Web 账号工具，不阻塞当前上传线程。"""
    threading.Thread(
        target=_run_grok2api_web_account_tools_background,
        args=(base_url, username, password, email),
        name="grok2api-web-account-tools",
        daemon=True,
    ).start()


def upload_grok2api_document_remote(
    base_url: str,
    username: str,
    password: str,
    endpoint: str,
    filename: str,
    document: dict,
) -> dict:
    """登录 Grok2API 后以 CurlMime multipart 上传 Web 或 Build 账号文档。"""
    base = str(base_url or "").strip().rstrip("/")
    access_token = _get_grok2api_admin_token(base, username, password)
    # CurlMime 对齐 Grok2API 管理后台的 multipart/form-data 文件上传格式。
    multipart = CurlMime()
    try:
        multipart.addpart(
            name="files",
            filename=filename,
            content_type="application/json",
            data=json.dumps(document, ensure_ascii=False).encode("utf-8"),
        )
        response = requests.post(
            f"{base}{endpoint}",
            headers={
                "Authorization": f"Bearer {access_token}",
                "Accept": "text/event-stream",
            },
            multipart=multipart,
            timeout=120,
            proxies={},
            impersonate="chrome",
        )
    finally:
        # 请求结束后必须释放 libcurl MIME 资源，避免批量注册持续占用内存。
        multipart.close()
    if response.status_code == 401:
        _invalidate_grok2api_admin_token(base, username, password)
    result = _parse_grok2api_import_stream(response, "Grok2API 账号导入")
    if endpoint.rstrip("/") == "/api/admin/v1/accounts/web/import":
        accounts = document.get("accounts") if isinstance(document, dict) else None
        web_account = accounts[0] if isinstance(accounts, list) and accounts else None
        email = (
            str(web_account.get("email") or "").strip()
            if isinstance(web_account, dict)
            else ""
        )
        if email:
            _start_grok2api_web_account_tools_background(
                base,
                username,
                password,
                email,
            )
    return result


def _run_remote_upload_with_retries(
    label: str,
    operation,
    log_callback=None,
) -> bool:
    """执行一次远程上传并在失败后额外重试三次，返回最终成功状态。"""
    total_attempts = REMOTE_UPLOAD_RETRIES + 1
    for attempt in range(1, total_attempts + 1):
        try:
            operation()
            if log_callback:
                log_callback(f"{label}远程上传成功")
            return True
        except Exception as exc:
            if log_callback:
                if attempt < total_attempts:
                    log_callback(
                        f"{label}远程上传失败: {exc}；"
                        f"准备重试 {attempt}/{REMOTE_UPLOAD_RETRIES}"
                    )
                else:
                    log_callback(
                        f"{label}远程上传失败，已用完 "
                        f"{REMOTE_UPLOAD_RETRIES} 次重试: {exc}"
                    )
            if attempt < total_attempts:
                time.sleep(min(2 ** (attempt - 1), 4))
    return False


def _deliver_cpa_record(
    record: dict,
    auth_dir: str,
    remote_url: str,
    management_key: str,
    log_callback=None,
) -> bool:
    """将 CPA auth 远程优先交付，远程不可用时才写入本地备用目录。"""
    remote_ok = False
    if remote_url and management_key:
        remote_ok = _run_remote_upload_with_retries(
            "CPA ",
            lambda: _s2cpa.upload_cpa_auth_remote(
                remote_url,
                management_key,
                record,
                proxy="",
            ),
            log_callback=log_callback,
        )
    elif remote_url or management_key:
        if log_callback:
            log_callback("CPA 远程配置不完整，改用本地备用目录")
    elif log_callback:
        log_callback("CPA 未配置远程服务器，使用本地备用目录")
    if remote_ok:
        return True
    if not auth_dir:
        if log_callback:
            log_callback("CPA 远程失败且未配置本地备用目录")
        return False
    try:
        path = _s2cpa.write_cpa_auth(_s2cpa.Path(auth_dir), record)
        if log_callback:
            log_callback(f"CPA 已降级写入本地 {path}")
        return True
    except Exception as exc:
        if log_callback:
            log_callback(f"CPA 本地备用写入失败: {exc}")
        return False


def _deliver_grok2api_document(
    label: str,
    endpoint: str,
    filename: str,
    document: dict,
    local_writer,
    log_callback=None,
) -> bool:
    """将 Grok2API 文档远程优先交付，失败时调用对应 Web/Build 本地写入器。"""
    remote_url = str(config.get("grok2api_remote_url", "") or "").strip()
    admin_username = str(
        config.get("grok2api_admin_username", "") or ""
    ).strip()
    admin_password = str(config.get("grok2api_admin_password", "") or "")
    remote_ok = False
    if remote_url and admin_username and admin_password:
        remote_ok = _run_remote_upload_with_retries(
            f"Grok2API {label} ",
            lambda: upload_grok2api_document_remote(
                remote_url,
                admin_username,
                admin_password,
                endpoint,
                filename,
                document,
            ),
            log_callback=log_callback,
        )
    elif remote_url or admin_username or admin_password:
        if log_callback:
            log_callback(
                f"Grok2API {label} 远程配置不完整，改用本地备用目录"
            )
    elif log_callback:
        log_callback(f"Grok2API {label} 未配置远程服务器，使用本地备用目录")
    if remote_ok:
        return True

    local_dir = str(config.get("grok2api_auth_dir", "") or "").strip()
    if local_dir and not os.path.isabs(local_dir):
        local_dir = os.path.join(APP_DIR, local_dir)
    if not local_dir:
        if log_callback:
            log_callback(
                f"Grok2API {label} 远程失败且未配置本地备用目录"
            )
        return False
    try:
        path = local_writer(_s2cpa.Path(local_dir))
        if log_callback:
            log_callback(f"Grok2API {label} 已降级写入本地 {path}")
        return True
    except Exception as exc:
        if log_callback:
            log_callback(f"Grok2API {label} 本地备用写入失败: {exc}")
        return False


def _append_sso_pending(email: str, sso: str, log_callback=None):
    """CPA 失败时保留 SSO，便于事后 sso_to_auth_json 重转。"""
    try:
        path = accounts_side_file("sso_pending.txt")
        line = f"{email}----{sso}\n" if email else f"{sso}\n"
        with open(path, "a", encoding="utf-8") as f:
            f.write(line)
        if log_callback:
            log_callback(f"[CPA] 已追加待重转 SSO → {path}")
    except Exception as exc:
        if log_callback:
            log_callback(f"[CPA] 写入 sso_pending 失败: {exc}")


def _append_sso_risk_rejected(email: str, sso: str, details: str, log_callback=None):
    """保存注册风控拒绝的 SSO；该类账号不进入待重转队列。"""
    try:
        path = accounts_side_file("sso_risk_rejected.txt")
        safe_details = re.sub(r"[\r\n\t]+", " ", str(details or "")).strip()
        with open(path, "a", encoding="utf-8") as f:
            f.write(f"{email}----{sso}----{safe_details}\n")
        if log_callback:
            log_callback(f"[CPA] 已保存注册风控拒绝记录 → {path}")
    except Exception as exc:
        if log_callback:
            log_callback(f"[CPA] 保存注册风控拒绝记录失败: {exc}")


def ensure_sso_oauth_eligible(raw_token, email="", log_callback=None) -> dict:
    """检查新账号是否被注册风控拒绝；无法判定时继续原有 OAuth 路径。"""
    if not config.get("cpa_auto_add", False):
        return {}
    if not has_selected_auth_output_target():
        return {}
    sso = _normalize_sso_token(raw_token)
    if not sso:
        raise RegistrationRiskDenied("注册风控检查失败: sso 为空")

    def _risk_log(message):
        """为风控探测日志追加 CPA 前缀并转交当前注册 worker。"""
        if log_callback:
            log_callback(f"[CPA] {str(message).strip()}")

    _risk_log("检查新账号注册风控状态 ...")
    state = _s2cpa.inspect_sso_account_state(
        sso,
        proxy=_resolve_cpa_proxy(),
        log=_risk_log,
    )
    if state.get("denied"):
        details = str(state.get("bot_flag_details") or "policy=deny,event=$registration")
        _append_sso_risk_rejected(email, sso, details, log_callback=log_callback)
        try:
            _bf = state.get("bot_flag_source")
            _rk = None
            _mrisk = re.search(r"risk=([\d.]+)", str(details))
            if _mrisk:
                try:
                    _rk = float(_mrisk.group(1))
                except Exception:
                    _rk = None
            record_register_result(
                "risk",
                email or "",
                kind=FAIL_RISK,
                detail=f"botFlagSource={_bf} {details}",
                bot_flag=_bf,
                risk=_rk,
                log_callback=log_callback,
            )
        except Exception:
            pass
        raise RegistrationRiskDenied(
            "注册风控拒绝，已跳过 OAuth: "
            f"botFlagSource={state.get('bot_flag_source')} {details}"
        )
    if not state.get("found"):
        _risk_log(f"未读取到注册风控字段，继续 OAuth: {state.get('error') or 'unknown'}")
    return state


def add_sso_to_cpa(raw_token, email="", log_callback=None) -> bool:
    """按独立开关将 SSO/OAuth 远程优先写入 CPA 与 Grok2API。

    先完成 OAuth 换取与文档转换，再并行交付所有已勾选目标。OAuth 失败时，
    会等换取流程结束后单独交付 Web SSO。每个远程目标独立重试和本地降级。
    """
    if not config.get("cpa_auto_add", False):
        if log_callback:
            log_callback("[*] 已关闭 SSO→auth，仅保存 SSO（不写 auth）")
        return True
    cpa_enabled, grok2api_enabled = get_auth_output_selection()
    if not cpa_enabled and not grok2api_enabled:
        if log_callback:
            log_callback("[*] CPA 与 Grok2API 均未勾选，跳过 SSO→auth 输出")
        return True

    auth_dir = str(config.get("cpa_auth_dir", "") or "").strip()
    remote_url = str(config.get("cpa_remote_url", "") or "").strip()
    management_key = str(config.get("cpa_management_key", "") or "").strip()
    if auth_dir and not os.path.isabs(auth_dir):
        auth_dir = os.path.join(APP_DIR, auth_dir)

    sso = _normalize_sso_token(raw_token)
    if not sso:
        return False
    proxy = _resolve_cpa_proxy()

    def _auth_log(message):
        """为 OAuth 和目标交付日志追加统一前缀。"""
        if log_callback:
            log_callback(f"[Auth] {str(message).strip()}")

    try:
        token_mode = str(
            config.get("cpa_token_mode", "device_protocol")
            or "device_protocol"
        ).lower()
        if token_mode not in ("device_protocol", "device_browser", "auth_code"):
            token_mode = "device_protocol"
        _mode_labels = {
            "device_protocol": "协议 Device Flow",
            "device_browser": "浏览器 Device Flow",
            "auth_code": "Authorization Code",
        }
        proxy_label = redact_proxy(proxy) or "直连"
        resin_label = (
            f", Resin Account={get_thread_resin_account()}"
            if get_thread_resin_account()
            else ""
        )
        _auth_log(
            f"SSO → {_mode_labels.get(token_mode, token_mode)} "
            f"换 token (proxy={proxy_label}{resin_label}) ..."
        )

        def _browser_approve(user_code, open_url):
            """在浏览器 Device Flow 模式中复用活动页面确认授权。"""
            return authorize_device_in_browser(
                user_code,
                open_url,
                timeout=10,
                log_callback=log_callback,
                cancel_callback=None,
            )

        # device_browser 模式：需要活动浏览器来点「继续/允许」
        # device_protocol 模式：纯 HTTP 协议换 token，不依赖浏览器
        # auth_code 模式：走授权码流程
        use_browser = token_mode == "device_browser" and _active_page() is not None
        if token_mode == "device_browser" and not use_browser:
            _auth_log("无活动浏览器，回退到协议 Device Flow")
            token_mode = "device_protocol"

        # sso_to_token 的 prefer 只区分 device / auth_code
        # browser_approve 是否传入决定走浏览器还是协议
        prefer = "auth_code" if token_mode == "auth_code" else "device"
        browser_cb = _browser_approve if use_browser else None

        token = _s2cpa.sso_to_token(
            sso,
            proxy=proxy,
            log=_auth_log,
            prefer=prefer,
            allow_fallback=True,
            browser_approve=browser_cb,
        )
    except Exception as exc:
        token = None
        _auth_log(f"SSO 换 token 异常: {exc}")

    if not token:
        _auth_log("SSO 换 token 失败；换取流程已结束，开始处理 Grok2API Web SSO")
        grok2api_web_ok = True
        if grok2api_enabled:
            try:
                web_document = _s2cpa.sso_to_grok2api_web_document(
                    sso,
                    email=email,
                )
                web_filename = _s2cpa.grok2api_web_auth_filename(
                    sso,
                    email=email,
                )

                def _write_failed_auth_web_fallback(local_dir):
                    """OAuth 失败时把 Web SSO 写入 Grok2API 本地备用目录。"""
                    return _s2cpa.write_grok2api_web_auth(
                        local_dir,
                        sso,
                        email=email,
                    )

                grok2api_web_ok = _deliver_grok2api_document(
                    "Web SSO",
                    "/api/admin/v1/accounts/web/import",
                    web_filename,
                    web_document,
                    _write_failed_auth_web_fallback,
                    log_callback=_auth_log,
                )
            except Exception as exc:
                grok2api_web_ok = False
                _auth_log(f"Grok2API Web SSO 准备失败: {exc}")
        if cpa_enabled or not grok2api_web_ok:
            _append_sso_pending(email, sso, log_callback=log_callback)
        return grok2api_web_ok and not cpa_enabled

    access_payload = _s2cpa.decode_jwt_payload(
        str(token.get("access_token") or token.get("key") or "")
    )
    access_referrer = access_payload.get("referrer")
    if access_referrer:
        _auth_log(f"access_token referrer={access_referrer!r}")

    # 每个状态只代表对应目标；未勾选的目标视为无需交付。
    delivery_status = {
        "cpa": not cpa_enabled,
        "grok2api_web": not grok2api_enabled,
        "grok2api_build": not grok2api_enabled,
    }
    # 先完成全部文档转换，再统一启动上传，避免 Web SSO 抢在 auth 之前发送。
    delivery_tasks = []
    if cpa_enabled:
        try:
            record = _s2cpa.token_to_cpa_record(token, email=email, sso=sso)
            delivery_tasks.append(
                (
                    "cpa",
                    "CPA",
                    _deliver_cpa_record,
                    (record, auth_dir, remote_url, management_key),
                    {"log_callback": _auth_log},
                )
            )
        except Exception as exc:
            delivery_status["cpa"] = False
            _auth_log(f"CPA OAuth 凭据格式转换失败: {exc}")

    if grok2api_enabled:
        try:
            web_document = _s2cpa.sso_to_grok2api_web_document(
                sso,
                email=email,
            )
            web_filename = _s2cpa.grok2api_web_auth_filename(
                sso,
                email=email,
            )

            def _write_web_fallback(local_dir):
                """把远程交付失败的 Web SSO 写入 Grok2API 本地备用目录。"""
                return _s2cpa.write_grok2api_web_auth(
                    local_dir,
                    sso,
                    email=email,
                )

            delivery_tasks.append(
                (
                    "grok2api_web",
                    "Grok2API Web SSO",
                    _deliver_grok2api_document,
                    (
                        "Web SSO",
                        "/api/admin/v1/accounts/web/import",
                        web_filename,
                        web_document,
                        _write_web_fallback,
                    ),
                    {"log_callback": _auth_log},
                )
            )
        except Exception as exc:
            delivery_status["grok2api_web"] = False
            _auth_log(f"Grok2API Web SSO 准备失败: {exc}")

        try:
            build_account = _s2cpa.token_to_grok2api_account(
                token,
                email=email,
            )
            build_document = {"accounts": [build_account]}
            build_filename = _s2cpa.grok2api_auth_filename(
                build_account,
                email=email,
            )

            def _write_build_fallback(local_dir):
                """把远程交付失败的 Build OAuth 写入 Grok2API 本地备用目录。"""
                return _s2cpa.write_grok2api_auth(
                    local_dir,
                    token,
                    email=email,
                )

            delivery_tasks.append(
                (
                    "grok2api_build",
                    "Grok2API Build OAuth",
                    _deliver_grok2api_document,
                    (
                        "Build OAuth",
                        "/api/admin/v1/accounts/import",
                        build_filename,
                        build_document,
                        _write_build_fallback,
                    ),
                    {"log_callback": _auth_log},
                )
            )
        except Exception as exc:
            delivery_status["grok2api_build"] = False
            _auth_log(f"Grok2API Build OAuth 准备失败: {exc}")

    if delivery_tasks:
        task_names = " / ".join(task[1] for task in delivery_tasks)
        _auth_log(f"auth 转换完成，开始并行交付: {task_names}")
        with concurrent.futures.ThreadPoolExecutor(
            max_workers=len(delivery_tasks),
            thread_name_prefix="auth-delivery",
        ) as executor:
            # future 映射保留业务目标，任一任务异常不会影响其他上传与兜底。
            future_targets = {
                executor.submit(task[2], *task[3], **task[4]): (task[0], task[1])
                for task in delivery_tasks
            }
            for future in concurrent.futures.as_completed(future_targets):
                target_key, target_label = future_targets[future]
                try:
                    delivery_status[target_key] = bool(future.result())
                except Exception as exc:
                    delivery_status[target_key] = False
                    _auth_log(f"{target_label} 交付线程异常: {exc}")

    all_delivered = all(delivery_status.values())
    if not all_delivered:
        _auth_log("部分选中目标在远程重试和本地降级后仍未写入成功")
        _append_sso_pending(email, sso, log_callback=log_callback)
    return all_delivered


def persist_submitted_outlook_account(email, profile, log_callback=None):
    """在确认资料已提交后保存恢复凭据，并立即把 OutlookEmail 项目邮箱标记成功。

    队列先于远端结算写入，确保进程随后在 SSO 等待阶段退出时仍能通过邮箱密码
    恢复账号；非 OutlookEmail 提供商不会产生队列或结算副作用。
    """
    if get_email_provider() != "outlook_email":
        return False
    password = str((profile or {}).get("password", "") or "")
    try:
        queue_sso_recovery(
            email,
            password,
            detail="注册资料已提交，等待首次获取 SSO",
            log_callback=log_callback,
        )
    except Exception as exc:
        # 账号已经创建，不能因本地文件异常把邮箱释放；继续等待当前浏览器直接取得 SSO。
        if log_callback:
            log_callback(f"[!] 待恢复 SSO 凭据保存失败，将继续当前取 SSO 流程: {exc}")
    try:
        finalize_email_provider_claim(
            "success",
            detail="Grok 注册资料已提交，邮箱已被账号占用",
            log_callback=log_callback,
        )
    except Exception as exc:
        # 远端结算失败不应打断已经创建的账号；外层 finally 会使用 success 再重试一次。
        if log_callback:
            log_callback(f"[!] OutlookEmail 已建号结算暂时失败，将在本轮结束重试: {exc}")
        return False
    return True


def save_grok_account_file(email, password, sso, file_lock=None):
    """把邮箱、Grok 密码和 SSO 写入独立账号文件，并限制文件权限为 0600。"""
    normalized_email = str(email or "").strip()
    normalized_password = str(password or "")
    normalized_sso = _normalize_sso_token(sso)
    if not normalized_email or not normalized_password or not normalized_sso:
        raise ValueError("保存 Grok 账号时缺少邮箱、密码或 SSO")
    path = account_file_for_email(normalized_email)
    line = f"{normalized_email}----{normalized_password}----{normalized_sso}\n"

    def _write_account_file():
        """执行单文件覆盖写入，并在支持权限位的平台限制其他用户读取。"""
        with open(path, "w", encoding="utf-8", newline="\n") as account_file:
            account_file.write(line)
        try:
            os.chmod(path, 0o600)
        except OSError:
            pass

    if file_lock:
        with file_lock:
            _write_account_file()
    else:
        _write_account_file()
    return path


def finalize_acquired_sso_account(
    email,
    password,
    sso,
    log_callback=None,
    file_lock=None,
):
    """持久化已取得的 SSO 并执行现有 OAuth/Build 交付，返回全部所选交付是否成功。

    一旦取得 SSO 就移出邮箱密码恢复队列；即使风控检查、文件写入或 Build 换取
    失败，也只保留现有 SSO 待处理记录，不会在下次注册时重复邮箱密码登录。
    """
    normalized_sso = _normalize_sso_token(sso)
    if not normalized_sso:
        raise ValueError("已获取 SSO 的账号缺少有效 Cookie")
    try:
        ensure_sso_oauth_eligible(
            normalized_sso,
            email=email,
            log_callback=log_callback,
        )
    except RegistrationRiskDenied:
        remove_sso_recovery(email, log_callback=log_callback)
        raise
    except Exception:
        _append_sso_pending(email, normalized_sso, log_callback=log_callback)
        remove_sso_recovery(email, log_callback=log_callback)
        raise
    try:
        save_grok_account_file(
            email,
            password,
            normalized_sso,
            file_lock=file_lock,
        )
    except Exception as file_exc:
        _append_sso_pending(email, normalized_sso, log_callback=log_callback)
        remove_sso_recovery(email, log_callback=log_callback)
        raise RuntimeError(f"保存账号文件失败: {file_exc}") from file_exc
    remove_sso_recovery(email, log_callback=log_callback)
    return add_sso_to_cpa(
        normalized_sso,
        email=email,
        log_callback=log_callback,
    )


def recover_pending_sso_accounts(log_callback=None, cancel_callback=None):
    """逐个登录独立任务领取的待恢复账号，成功后保存 SSO 并执行现有交付流程。

    每条记录在一个程序批次中最多尝试一次。临时失败会保留邮箱和密码并累计错误，
    供用户再次点击恢复按钮；每个恢复账号使用独立浏览器会话，避免 Cookie 串号。
    该流程只使用本地保存的 Grok 凭据，不依赖当前邮箱提供商或邮箱 API。
    """
    recovered = 0
    failed = 0
    while True:
        raise_if_cancelled(cancel_callback)
        record = claim_next_sso_recovery()
        if not record:
            break
        email = str(record.get("email", "") or "").strip().lower()
        password = str(record.get("password", "") or "")
        sso_acquired = False
        if log_callback:
            log_callback(
                f"--- 恢复待获取 SSO 账号: {email} "
                f"(历史尝试 {int(record.get('attempts', 0) or 0)} 次) ---"
            )
        try:
            try:
                stop_browser()
            except Exception:
                pass
            start_browser(log_callback=log_callback)
            login_grok_with_email_password(
                email,
                password,
                timeout=45,
                log_callback=log_callback,
                cancel_callback=cancel_callback,
            )
            sso = wait_for_sso_cookie(
                timeout=35,
                log_callback=log_callback,
                cancel_callback=cancel_callback,
            )
            sso_acquired = True
            delivery_ok = finalize_acquired_sso_account(
                email,
                password,
                sso,
                log_callback=log_callback,
            )
            # finalize_acquired_sso_account 已删除磁盘队列；这里再次调用只清理并发领取状态。
            remove_sso_recovery(email)
            recovered += 1
            record_register_result(
                "ok",
                email,
                kind="sso_recovered",
                detail=(
                    "邮箱密码登录恢复 SSO 成功"
                    if delivery_ok
                    else "邮箱密码登录恢复 SSO 成功，所选 auth 输出存在失败"
                ),
                log_callback=log_callback,
            )
            if log_callback:
                suffix = "" if delivery_ok else "（所选 auth 输出存在失败）"
                log_callback(f"[+] SSO 恢复成功{suffix}: {email}")
        except RegistrationCancelled:
            if sso_acquired:
                remove_sso_recovery(email, log_callback=log_callback)
            else:
                finish_sso_recovery_attempt(email, "用户停止 SSO 恢复")
            raise
        except Exception as exc:
            failed += 1
            if sso_acquired:
                # SSO 已取得后无论风控、保存或 Build 如何结束，都不再回到登录恢复队列。
                remove_sso_recovery(email, log_callback=log_callback)
            else:
                finish_sso_recovery_attempt(email, str(exc))
            kind = classify_failure(exc)
            record_register_result(
                "fail",
                email,
                kind=kind,
                detail=str(exc)[:300],
                log_callback=log_callback,
            )
            if log_callback:
                if sso_acquired:
                    log_callback(
                        f"[!] 已取得 SSO，但后续保存或 auth 输出失败；"
                        f"不再自动登录恢复: {email} | {exc}"
                    )
                else:
                    log_callback(
                        f"[!] SSO 恢复本轮失败，已保留供下次点击恢复: {email} | {exc}"
                    )
        finally:
            try:
                stop_browser()
            except Exception:
                pass
    if log_callback and (recovered or failed):
        log_callback(f"[*] 待恢复 SSO 本轮结束：成功 {recovered} | 失败 {failed}")
    return {"success": recovered, "failed": failed}


# create_browser_options -> browser_session

def _build_request_kwargs(**kwargs):
    request_kwargs = dict(kwargs)
    proxies = request_kwargs.pop("proxies", None)
    if proxies is None:
        proxies = get_proxies()
    if proxies:
        request_kwargs["proxies"] = proxies
    request_kwargs.setdefault("timeout", 15)
    return request_kwargs


def http_get(url, **kwargs):
    allow_direct_fallback = bool(kwargs.pop("_allow_direct_fallback", True))
    if _url_needs_direct(url):
        rk = dict(kwargs)
        rk.pop("proxies", None)
        rk.setdefault("timeout", 20)
        clean = {k: v for k, v in rk.items() if k != "impersonate"}
        return _std_requests.get(url, proxies={}, **clean)
    try:
        rk = _build_request_kwargs(**kwargs)
        return requests.get(url, **rk)
    except Exception as exc:
        err = str(exc)
        if allow_direct_fallback and any(x in err for x in ("Could not connect", "TLS connect error", "OPENSSL_internal", "7890")):
            rk = dict(kwargs)
            rk.pop("proxies", None)
            rk.setdefault("timeout", 20)
            clean = {k: v for k, v in rk.items() if k != "impersonate"}
            return _std_requests.get(url, proxies={}, **clean)
        raise



def http_post(url, **kwargs):
    if _url_needs_direct(url):
        rk = dict(kwargs)
        rk.pop("proxies", None)
        rk.setdefault("timeout", 20)
        clean = {k: v for k, v in rk.items() if k != "impersonate"}
        return _std_requests.post(url, proxies={}, **clean)
    try:
        rk = _build_request_kwargs(**kwargs)
        if "_apply_mail_direct" in globals():
            rk = _apply_mail_direct(url, rk)
        return requests.post(url, **rk)
    except Exception as exc:
        err = str(exc)
        if any(x in err for x in ("Could not connect", "TLS connect error", "OPENSSL_internal", "7890")):
            rk = dict(kwargs)
            rk.pop("proxies", None)
            rk.setdefault("timeout", 20)
            clean = {k: v for k, v in rk.items() if k != "impersonate"}
            return _std_requests.post(url, proxies={}, **clean)
        raise



def http_delete(url, **kwargs):
    try:
        rk = _apply_mail_direct(url, _build_request_kwargs(**kwargs))
        return requests.delete(url, **rk)
    except Exception as exc:
        err = str(exc)
        if (
            "127.0.0.1 port 7890" in err
            or "Could not connect to server" in err
            or "TLS connect error" in err
            or "OPENSSL_internal" in err
        ):
            retry_kwargs = dict(kwargs)
            retry_kwargs["proxies"] = {}
            return requests.delete(url, **_build_request_kwargs(**retry_kwargs))
        raise



def raise_if_cancelled(cancel_callback=None):
    if cancel_callback and cancel_callback():
        raise RegistrationCancelled("用户停止注册")


def sleep_with_cancel(seconds, cancel_callback=None):
    deadline = time.time() + max(seconds, 0)
    while True:
        raise_if_cancelled(cancel_callback)
        remaining = deadline - time.time()
        if remaining <= 0:
            return
        time.sleep(min(0.2, remaining))


def run_startup_checks_with_xai_retries(
    source_config,
    batch_id,
    log_callback=None,
    cancel_callback=None,
):
    """执行启动连通性检查，并对 xAI 注册页最多重试三次。

    第一次执行代理、xAI、邮箱和输出目标的完整检查；后续只重试 xAI，避免重复
    探测无关服务。普通代理沿用同一入口重新建立请求，适配动态出口；Resin
    每次使用新的 Account 代次。返回最终检查结果、成功或最后一次使用的 Resin
    代次，以及实际尝试次数，供首个注册 worker 复用已验证出口。
    """
    checks = []
    attempts_used = 0
    final_generation = 0
    resin_mode = is_resin_proxy_mode(source_config)

    for attempt in range(1, XAI_STARTUP_CHECK_ATTEMPTS + 1):
        raise_if_cancelled(cancel_callback)
        generation = attempt - 1 if resin_mode else 0
        final_generation = generation
        account = (
            resin_account_id(batch_id, 0, 0, generation)
            if resin_mode
            else ""
        )
        check_config = connectivity_config_for_proxy(source_config, account)
        if attempt == 1:
            checks = _conn.run_connectivity_checks(
                check_config,
                http_get,
                http_post,
            )
        else:
            xai_check = _conn.check_xai_signup(
                str(check_config.get("proxy", "") or ""),
                http_get,
            )
            replaced = False
            updated_checks = []
            for name, ok, detail in checks:
                if name == _conn.XAI_SIGNUP_CHECK_NAME:
                    updated_checks.append(xai_check)
                    replaced = True
                else:
                    updated_checks.append((name, ok, detail))
            if not replaced:
                updated_checks.append(xai_check)
            checks = updated_checks

        attempts_used = attempt
        xai_result = next(
            (
                item
                for item in checks
                if item[0] == _conn.XAI_SIGNUP_CHECK_NAME
            ),
            None,
        )
        if xai_result is None:
            raise RuntimeError("启动检查没有返回 xAI 注册页结果")

        _, xai_ok, xai_detail = xai_result
        route_detail = (
            f"Resin Account={account}"
            if resin_mode
            else "普通代理新连接"
        )
        if xai_ok:
            if attempt > 1 and log_callback:
                log_callback(
                    f"[检查] [OK] {_conn.XAI_SIGNUP_CHECK_NAME}"
                    f"（尝试 {attempt}/{XAI_STARTUP_CHECK_ATTEMPTS}，"
                    f"{route_detail}）: {xai_detail}"
                )
            return checks, final_generation, attempts_used

        if log_callback:
            log_callback(
                f"[检查] [FAIL] {_conn.XAI_SIGNUP_CHECK_NAME}"
                f"（尝试 {attempt}/{XAI_STARTUP_CHECK_ATTEMPTS}，"
                f"{route_detail}）: {xai_detail}"
            )
        if attempt < XAI_STARTUP_CHECK_ATTEMPTS:
            sleep_with_cancel(1.0, cancel_callback)

    return checks, final_generation, attempts_used


def get_domains(api_key=None):
    return duckmail_provider.get_domains(
        http_get,
        get_duckmail_api_base(),
        api_key=api_key or get_duckmail_api_key(),
    )


def create_account(address, password, api_key=None, expires_in=0):
    return duckmail_provider.create_account(
        http_post,
        get_duckmail_api_base(),
        address,
        password,
        api_key=api_key or get_duckmail_api_key(),
        expires_in=expires_in,
    )


def get_token(address, password):
    return duckmail_provider.get_token(
        http_post,
        get_duckmail_api_base(),
        address,
        password,
    )


def get_messages(token):
    return duckmail_provider.get_messages(
        http_get,
        get_duckmail_api_base(),
        token,
    )


def get_message_detail(token, message_id):
    return duckmail_provider.get_message_detail(
        http_get,
        get_duckmail_api_base(),
        token,
        message_id,
    )



def cloudflare_get_domains(api_base, api_key=None):
    return cloudflare_provider.get_domains(
        http_get,
        api_base,
        domains_path=get_cloudflare_path("cloudflare_path_domains", "/domains"),
        api_key=api_key or get_cloudflare_api_key(),
        auth_mode=get_cloudflare_auth_mode(),
        custom_auth=get_cloudflare_custom_auth(),
    )


def cloudflare_create_account(api_base, address, password, api_key=None, expires_in=0):
    return cloudflare_provider.create_account(
        http_post,
        api_base,
        address,
        password,
        accounts_path=get_cloudflare_path("cloudflare_path_accounts", "/accounts"),
        api_key=api_key or get_cloudflare_api_key(),
        auth_mode=get_cloudflare_auth_mode(),
        custom_auth=get_cloudflare_custom_auth(),
        expires_in=expires_in,
    )


def cloudflare_get_token(api_base, address, password, api_key=None):
    return cloudflare_provider.get_token(
        http_post,
        api_base,
        address,
        password,
        token_path=get_cloudflare_path("cloudflare_path_token", "/token"),
        api_key=api_key or get_cloudflare_api_key(),
        auth_mode=get_cloudflare_auth_mode(),
        custom_auth=get_cloudflare_custom_auth(),
    )


def cloudflare_get_messages(api_base, token):
    return cloudflare_provider.get_messages(
        http_get,
        api_base,
        token,
        messages_path=get_cloudflare_path("cloudflare_path_messages", "/messages"),
        api_key=get_cloudflare_api_key(),
        auth_mode=get_cloudflare_auth_mode(),
        custom_auth=get_cloudflare_custom_auth(),
    )


def cloudflare_get_message_detail(api_base, token, message_id):
    return cloudflare_provider.get_message_detail(
        http_get,
        api_base,
        token,
        message_id,
        messages_path=get_cloudflare_path("cloudflare_path_messages", "/messages"),
        api_key=get_cloudflare_api_key(),
        auth_mode=get_cloudflare_auth_mode(),
        custom_auth=get_cloudflare_custom_auth(),
    )


YYDS_API_BASE = yyds_provider.API_BASE


def get_yyds_api_key():
    return config.get("yyds_api_key", "")


def get_yyds_jwt():
    return config.get("yyds_jwt", "")


def get_yyds_default_domain():
    return str(config.get("yyds_default_domain", "") or "").strip()


def yyds_get_domains(api_key=None, jwt=None):
    return yyds_provider.get_domains(http_get, api_key=api_key or get_yyds_api_key(), jwt=jwt or get_yyds_jwt())


def yyds_create_account(local_part=None, domain=None, api_key=None, jwt=None):
    return yyds_provider.create_account(
        http_post,
        local_part=local_part or "",
        domain=domain or "",
        api_key=api_key or get_yyds_api_key(),
        jwt=jwt or get_yyds_jwt(),
    )


def yyds_get_token(address, api_key=None, jwt=None):
    return yyds_provider.get_token(http_post, address, api_key=api_key or get_yyds_api_key(), jwt=jwt or get_yyds_jwt())


def yyds_get_messages(address, token=None, api_key=None, jwt=None):
    return yyds_provider.get_messages(
        http_get,
        address,
        token=token or "",
        api_key=api_key or get_yyds_api_key(),
        jwt=jwt or get_yyds_jwt(),
    )


def yyds_get_message_detail(message_id, token=None, api_key=None, jwt=None):
    return yyds_provider.get_message_detail(
        http_get,
        message_id,
        token=token or "",
        api_key=api_key or get_yyds_api_key(),
        jwt=jwt or get_yyds_jwt(),
    )


def yyds_generate_username(length=10):
    return yyds_provider.generate_username(length)


def yyds_pick_domain(api_key=None, jwt=None):
    return yyds_provider.pick_domain(http_get, api_key=api_key or get_yyds_api_key(), jwt=jwt or get_yyds_jwt())


def yyds_get_email_and_token(api_key=None, jwt=None):
    key = api_key or get_yyds_api_key()
    token = jwt or get_yyds_jwt()
    if not token and not key:
        raise Exception("YYDS API Key 或 JWT 未配置")
    domain = get_yyds_default_domain() or yyds_pick_domain(api_key=key, jwt=token)
    username = yyds_generate_username(10)
    result = yyds_create_account(
        local_part=username, domain=domain, api_key=key, jwt=token
    )
    address = result.get("address") or f"{username}@{domain}"
    temp_token = result.get("token")
    if not temp_token:
        temp_token = yyds_get_token(address, api_key=key, jwt=token)
    if not temp_token:
        raise Exception("获取 YYDS token 失败")
    print(f"[*] 已创建 YYDS 邮箱: {address}")
    return address, temp_token


def yyds_get_oai_code(token, address, timeout=180, poll_interval=3, log_callback=None, jwt=None, cancel_callback=None):
    return yyds_provider.wait_for_code(
        http_get,
        token,
        address,
        timeout=timeout,
        poll_interval=poll_interval,
        jwt=jwt or get_yyds_jwt(),
        raise_if_cancelled=raise_if_cancelled,
        sleep_with_cancel=sleep_with_cancel,
        log_callback=log_callback,
        cancel_callback=cancel_callback,
    )



def generate_username(length=10):
    return _generate_username(length)


def pick_domain(api_key=None):
    return duckmail_provider.pick_domain(get_domains(api_key=api_key))


def get_cloudmail_url():
    return str(os.environ.get("CLOUDMAIL_URL") or config.get("cloudmail_url", "") or "").strip().rstrip("/")


def get_cloudmail_admin_email():
    return str(os.environ.get("CLOUDMAIL_ADMIN_EMAIL") or config.get("cloudmail_admin_email", "") or "").strip()


def get_cloudmail_password():
    return str(os.environ.get("CLOUDMAIL_PASSWORD") or config.get("cloudmail_password", "") or "")


def cloudmail_get_email_and_token():
    raw_domains = str(config.get("defaultDomains", "") or "")
    domains = [item.strip() for item in re.split(r"[,，\s]+", raw_domains) if item.strip()]
    return cloudmail_provider.create_mailbox(
        http_post,
        get_cloudmail_url(),
        get_cloudmail_admin_email(),
        get_cloudmail_password(),
        domains,
        username=generate_username(10),
    )


def cloudmail_get_oai_code(
    dev_token,
    email,
    timeout=180,
    poll_interval=3,
    log_callback=None,
    cancel_callback=None,
    resend_callback=None,
):
    del dev_token
    return cloudmail_provider.wait_for_code(
        http_post,
        http_delete,
        get_cloudmail_url(),
        get_cloudmail_admin_email(),
        get_cloudmail_password(),
        email,
        timeout=timeout,
        poll_interval=poll_interval,
        raise_if_cancelled=raise_if_cancelled,
        sleep_with_cancel=sleep_with_cancel,
        log_callback=log_callback,
        cancel_callback=cancel_callback,
        resend_callback=resend_callback,
    )


def get_icloud_hme_state_path():
    """返回 iCloud HME 保留邮箱记录路径，供以后按账号和邮箱继续查询。"""
    return accounts_side_file("icloud_hme_leases.json")


def icloud_hme_get_email_and_token(log_callback=None):
    """通过 icloud-hme 创建隐私邮箱并返回非敏感租约令牌。"""
    return icloud_hme_provider.create_mailbox(
        config,
        get_icloud_hme_state_path(),
        log_callback=log_callback,
    )


def icloud_hme_get_oai_code(
    dev_token,
    email,
    timeout=180,
    poll_interval=3,
    log_callback=None,
    cancel_callback=None,
    resend_callback=None,
):
    """按隐私邮箱精确轮询 iCloud IMAP 邮件并提取 xAI 验证码。"""
    return icloud_hme_provider.wait_for_code(
        config,
        get_icloud_hme_state_path(),
        dev_token,
        email,
        timeout=timeout,
        poll_interval=poll_interval,
        raise_if_cancelled=raise_if_cancelled,
        sleep_with_cancel=sleep_with_cancel,
        log_callback=log_callback,
        cancel_callback=cancel_callback,
        resend_callback=resend_callback,
    )


def outlook_email_get_email_and_token(log_callback=None):
    """从 OutlookEmail 的 Grok 项目领取邮箱并返回本地非敏感租约令牌。"""
    return outlook_email_provider.create_mailbox(config, log_callback=log_callback)


def outlook_email_get_oai_code(
    lease_token,
    email,
    timeout=180,
    poll_interval=3,
    log_callback=None,
    cancel_callback=None,
    resend_callback=None,
):
    """通过 OutlookEmail 完整 API 轮询领取邮箱的 xAI 验证码。"""
    return outlook_email_provider.wait_for_code(
        config,
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


def retain_email_provider_alias(log_callback=None):
    """结束当前 worker 的邮箱占用并永久保留 iCloud 别名及其本地记录。"""
    if get_email_provider() != "icloud":
        return True
    return icloud_hme_provider.retain_current_alias(
        config,
        get_icloud_hme_state_path(),
        log_callback=log_callback,
    )


def finalize_email_provider_claim(
    outcome="release",
    detail="",
    log_callback=None,
    stopped=False,
):
    """按注册阶段结算项目邮箱；停止时只释放资料尚未提交的领取。

    ``success`` 表示资料已确认提交且邮箱已被 Grok 账号占用，停止任务也必须保留；
    ``release`` 表示账号尚未创建，可恢复为 ``toClaim``；``failed`` 仅用于永久拒绝。
    """
    provider = get_email_provider()
    if provider == "outlook_email":
        if stopped and str(outcome or "").strip().lower() == "failed":
            outcome = "release"
            detail = "批次停止，释放尚未完成的邮箱领取"
        return outlook_email_provider.finalize_current_claim(
            config,
            outcome,
            detail=detail,
            log_callback=log_callback,
        )
    return retain_email_provider_alias(log_callback=log_callback)


def get_email_provider():
    """返回规范化后的邮箱提供商名称。"""
    return str(config.get("email_provider", "cloudflare") or "cloudflare").strip().lower()


def get_email_and_token(api_key=None, log_callback=None):
    """按当前 provider 创建邮箱并返回邮箱地址和后续收信令牌。"""
    provider = get_email_provider()
    if provider == "outlook_email":
        return outlook_email_get_email_and_token(log_callback=log_callback)
    if provider == "icloud":
        return icloud_hme_get_email_and_token(log_callback=log_callback)
    if provider == "yyds":
        return yyds_get_email_and_token(api_key=api_key, jwt=get_yyds_jwt())
    if provider == "cloudmail":
        return cloudmail_get_email_and_token()
    if provider == "cloudflare":
        api_base = get_cloudflare_api_base()
        if not api_base:
            raise Exception("Cloudflare API Base 未配置")
        try:
            # cloudflare_temp_email 专用模式
            return cloudflare_create_temp_address(api_base)
        except Exception as primary_exc:
            try:
                return cloudflare_provider.create_mailbox_fallback(
                    http_get,
                    http_post,
                    api_base,
                    domains_path=get_cloudflare_path("cloudflare_path_domains", "/domains"),
                    accounts_path=get_cloudflare_path("cloudflare_path_accounts", "/accounts"),
                    token_path=get_cloudflare_path("cloudflare_path_token", "/token"),
                    api_key=api_key or get_cloudflare_api_key(),
                    auth_mode=get_cloudflare_auth_mode(),
                    custom_auth=get_cloudflare_custom_auth(),
                )
            except Exception:
                raise Exception(f"Cloudflare 创建邮箱失败: {primary_exc}")
    if provider == "mailnest":
        return mailnest_buy_email(), "_"
    return duckmail_provider.create_mailbox(
        http_get,
        http_post,
        get_duckmail_api_base(),
        api_key=api_key or get_duckmail_api_key(),
        expires_in=0,
    )


def get_oai_code(
    dev_token,
    email,
    timeout=180,
    poll_interval=3,
    log_callback=None,
    cancel_callback=None,
    resend_callback=None,
):
    """按当前 provider 轮询注册验证码。"""
    provider = get_email_provider()
    if provider == "outlook_email":
        return outlook_email_get_oai_code(
            dev_token,
            email,
            timeout=timeout,
            poll_interval=poll_interval,
            log_callback=log_callback,
            cancel_callback=cancel_callback,
            resend_callback=resend_callback,
        )
    if provider == "icloud":
        return icloud_hme_get_oai_code(
            dev_token,
            email,
            timeout=timeout,
            poll_interval=poll_interval,
            log_callback=log_callback,
            cancel_callback=cancel_callback,
            resend_callback=resend_callback,
        )
    if provider == "yyds":
        return yyds_get_oai_code(
            dev_token,
            email,
            timeout=timeout,
            poll_interval=poll_interval,
            log_callback=log_callback,
            jwt=get_yyds_jwt(),
            cancel_callback=cancel_callback,
        )
    if provider == "cloudmail":
        return cloudmail_get_oai_code(
            dev_token,
            email,
            timeout=timeout,
            poll_interval=poll_interval,
            log_callback=log_callback,
            cancel_callback=cancel_callback,
            resend_callback=resend_callback,
        )
    if provider == "cloudflare":
        return cloudflare_get_oai_code(
            dev_token,
            email,
            timeout=timeout,
            poll_interval=poll_interval,
            log_callback=log_callback,
            cancel_callback=cancel_callback,
            resend_callback=resend_callback,
        )
    if provider == "mailnest":
        return mailnest_get_code(
            email,
            timeout=timeout,
            poll_interval=poll_interval,
            log_callback=log_callback,
            cancel_callback=cancel_callback,
        )
    return duckmail_get_oai_code(
        dev_token,
        email,
        timeout=timeout,
        poll_interval=poll_interval,
        log_callback=log_callback,
        cancel_callback=cancel_callback,
    )



def extract_verification_code(text, subject=""):
    return _extract_code(text, subject)


def duckmail_get_oai_code(
    dev_token,
    email,
    timeout=180,
    poll_interval=3,
    log_callback=None,
    cancel_callback=None,
):
    return duckmail_provider.wait_for_code(
        http_get,
        get_duckmail_api_base(),
        dev_token,
        email,
        timeout=timeout,
        poll_interval=poll_interval,
        extract_code=extract_verification_code,
        raise_if_cancelled=raise_if_cancelled,
        sleep_with_cancel=sleep_with_cancel,
        log_callback=log_callback,
        cancel_callback=cancel_callback,
    )


def cloudflare_get_oai_code(
    dev_token,
    email,
    timeout=180,
    poll_interval=3,
    log_callback=None,
    cancel_callback=None,
    resend_callback=None,
):
    return cloudflare_provider.wait_for_code(
        http_get,
        get_cloudflare_api_base(),
        dev_token,
        email,
        messages_path=get_cloudflare_path("cloudflare_path_messages", "/messages"),
        api_key=get_cloudflare_api_key(),
        auth_mode=get_cloudflare_auth_mode(),
        custom_auth=get_cloudflare_custom_auth(),
        timeout=timeout,
        poll_interval=poll_interval,
        raise_if_cancelled=raise_if_cancelled,
        sleep_with_cancel=sleep_with_cancel,
        log_callback=log_callback,
        cancel_callback=cancel_callback,
        resend_callback=resend_callback,
    )


def generate_random_birthdate():
    import datetime as dt

    today = dt.date.today()
    age = random.randint(20, 40)
    birth_year = today.year - age
    birth_month = random.randint(1, 12)
    birth_day = random.randint(1, 28)
    return f"{birth_year}-{birth_month:02d}-{birth_day:02d}T16:00:00.000Z"


def response_preview(res, limit=200):
    """安全预览 HTTP 响应体；gRPC/二进制内容不直接当文本打印。"""
    try:
        headers = {str(k).lower(): str(v).lower() for k, v in dict(getattr(res, "headers", {}) or {}).items()}
        content_type = headers.get("content-type", "")
        raw = getattr(res, "content", None)
        if raw is None:
            try:
                raw = (res.text or "").encode("utf-8", errors="replace")
            except Exception:
                raw = b""
        if not isinstance(raw, (bytes, bytearray)):
            raw = str(raw).encode("utf-8", errors="replace")
        raw = bytes(raw)

        # gRPC / protobuf 常见 content-type 或正文以不可打印字节为主
        is_binaryish = (
            "grpc" in content_type
            or "protobuf" in content_type
            or "octet-stream" in content_type
            or (raw[:1] in (b"\x00", b"\x01") and b"grpc-status" in raw)
        )
        if is_binaryish or (raw and sum(1 for b in raw[:64] if b < 9 or (13 < b < 32)) > 8):
            # 尽量抽出可读的 trailer 片段（如 grpc-status:0）
            readable = re.findall(rb"[ -~]{3,}", raw)
            text = " ".join(part.decode("ascii", errors="ignore") for part in readable)
            text = re.sub(r"\s+", " ", text).strip()
            if not text:
                text = f"<binary {len(raw)} bytes>"
            return text[:limit]

        try:
            text = raw.decode("utf-8")
        except UnicodeDecodeError:
            text = raw.decode("utf-8", errors="replace")
        text = re.sub(r"\s+", " ", text).strip()
        return text[:limit]
    except Exception:
        return ""


def is_cloudflare_block_response(res):
    try:
        headers = {str(k).lower(): str(v).lower() for k, v in dict(res.headers).items()}
        text = str(res.text or "").lower()
        server = headers.get("server", "")
        content_type = headers.get("content-type", "")
        return (
            res.status_code in (403, 429, 503)
            and (
                "cloudflare" in server
                or "cloudflare" in text
                or "cf-error" in text
                or "__cf_chl" in text
                or "text/html" in content_type
            )
        )
    except Exception:
        return False


def set_birth_date(session, log_callback=None):
    url = "https://grok.com/rest/auth/set-birth-date"
    new_headers = {
        "content-type": "application/json",
        "origin": "https://grok.com",
        "referer": "https://grok.com/",
    }
    payload = {"birthDate": generate_random_birthdate()}
    try:
        res = session.post(url, json=payload, headers=new_headers, timeout=15)
        body_preview = response_preview(res)
        if log_callback:
            log_callback(
                f"[Debug] set_birth_date status: {res.status_code}, body: {body_preview}"
            )
        if 200 <= res.status_code < 300:
            return True, "ok"
        # 生日一旦写过就不能改；算已完成，不能当失败中断后续 NSFW
        text = str(res.text or "")
        if res.status_code in (400, 409, 429) and (
            "birth-date-change-limit-reached" in text
            or "Birth date is locked" in text
            or "already set" in text.lower()
        ):
            return True, "already_set"
        if is_cloudflare_block_response(res):
            return (
                False,
                "set_birth_date 被 grok.com 的 Cloudflare 防护拦截，HTTP "
                f"{res.status_code}",
            )
        return False, f"set_birth_date HTTP {res.status_code}: {body_preview}"
    except Exception as e:
        if log_callback:
            log_callback(f"[set_birth_date] 异常: {e}")
        return False, f"set_birth_date 异常: {e}"


def set_tos_accepted(session, log_callback=None):
    url = "https://accounts.x.ai/auth_mgmt.AuthManagement/SetTosAcceptedVersion"
    payload = struct.pack("B", (2 << 3) | 0) + struct.pack("B", 1)
    data = b"\x00" + struct.pack(">I", len(payload)) + payload
    new_headers = {
        "content-type": "application/grpc-web+proto",
        "x-grpc-web": "1",
        "x-user-agent": "connect-es/2.1.1",
        "origin": "https://accounts.x.ai",
        "referer": "https://accounts.x.ai/accept-tos",
    }
    try:
        res = session.post(url, data=data, headers=new_headers, timeout=15)
        if log_callback:
            log_callback(f"[Debug] set_tos_accepted status: {res.status_code}")
        if 200 <= res.status_code < 300:
            return True, "ok"
        if is_cloudflare_block_response(res):
            return (
                False,
                "set_tos_accepted 被 accounts.x.ai 的 Cloudflare 防护拦截，HTTP "
                f"{res.status_code}",
            )
        return False, f"set_tos_accepted HTTP {res.status_code}: {response_preview(res)}"
    except Exception as e:
        if log_callback:
            log_callback(f"[set_tos_accepted] 异常: {e}")
        return False, f"set_tos_accepted 异常: {e}"


def encode_grpc_nsfw_settings():
    field1_content = bytes([0x10, 0x01])
    field1 = bytes([0x0A, len(field1_content)]) + field1_content
    nsfw_string = b"always_show_nsfw_content"
    field2_inner = bytes([0x0A, len(nsfw_string)]) + nsfw_string
    field2 = bytes([0x12, len(field2_inner)]) + field2_inner
    payload = field1 + field2
    return b"\x00" + struct.pack(">I", len(payload)) + payload


def update_nsfw_settings(session, log_callback=None):
    url = "https://grok.com/auth_mgmt.AuthManagement/UpdateUserFeatureControls"
    data = encode_grpc_nsfw_settings()
    new_headers = {
        "content-type": "application/grpc-web+proto",
        "x-grpc-web": "1",
        "origin": "https://grok.com",
        "referer": "https://grok.com/",
    }
    try:
        res = session.post(url, data=data, headers=new_headers, timeout=15)
        if log_callback:
            log_callback(
                f"[Debug] update_nsfw status: {res.status_code}, body: {response_preview(res)}"
            )
        if 200 <= res.status_code < 300:
            return True, "ok"
        if is_cloudflare_block_response(res):
            return (
                False,
                "update_nsfw_settings 被 grok.com 的 Cloudflare 防护拦截，HTTP "
                f"{res.status_code}",
            )
        return False, f"update_nsfw_settings HTTP {res.status_code}: {response_preview(res)}"
    except Exception as e:
        if log_callback:
            log_callback(f"[update_nsfw] 异常: {e}")
        return False, f"update_nsfw_settings 异常: {e}"


def enable_nsfw_via_browser(token="", log_callback=None):
    """在已登录的注册浏览器内调用 grok.com 接口，绕过外部 HTTP 的 CF 拦截。"""
    page_obj = _active_page()
    if page_obj is None:
        return False, "浏览器页面未就绪"

    birth = generate_random_birthdate()
    nsfw_bytes = encode_grpc_nsfw_settings()
    nsfw_b64 = base64.b64encode(nsfw_bytes).decode("ascii")

    try:
        if log_callback:
            log_callback("[*] 浏览器内开启 NSFW：打开 grok.com ...")
        # 确保 SSO cookie 在浏览器上下文中
        if token:
            try:
                page_obj.set.cookies(
                    [
                        {"name": "sso", "value": token, "domain": ".x.ai", "path": "/"},
                        {"name": "sso-rw", "value": token, "domain": ".x.ai", "path": "/"},
                        {"name": "sso", "value": token, "domain": ".grok.com", "path": "/"},
                        {"name": "sso-rw", "value": token, "domain": ".grok.com", "path": "/"},
                    ]
                )
            except Exception:
                try:
                    page_obj.run_js(
                        """
const token = arguments[0];
document.cookie = 'sso=' + token + '; path=/; domain=.grok.com';
document.cookie = 'sso-rw=' + token + '; path=/; domain=.grok.com';
                        """,
                        token,
                    )
                except Exception:
                    pass
        page_obj.get("https://grok.com/")
        try:
            page_obj.wait.doc_loaded()
        except Exception:
            pass
        # 等 CF 挑战结束，否则 fetch 也会拿到 Just a moment
        for i in range(25):
            try:
                title = str(page_obj.run_js("return document.title || '';") or "").lower()
                body = str(
                    page_obj.run_js(
                        "return (document.body && (document.body.innerText||'')) || '';"
                    )
                    or ""
                ).lower()
                if "just a moment" not in title and "just a moment" not in body[:200]:
                    if "checking your browser" not in body[:300]:
                        break
            except Exception:
                pass
            time.sleep(1.0)
        else:
            if log_callback:
                log_callback("[!] grok.com 仍停在 Cloudflare 挑战页，浏览器内 NSFW 可能失败")
        time.sleep(1.0)

        result = page_obj.run_js(
            r"""
const birthDate = arguments[0];
const nsfwB64 = arguments[1];
function b64ToBytes(b64) {
  const bin = atob(b64);
  const arr = new Uint8Array(bin.length);
  for (let i = 0; i < bin.length; i++) arr[i] = bin.charCodeAt(i);
  return arr;
}
return (async () => {
  const out = { birthStatus: 0, birthBody: '', nsfwStatus: 0, nsfwBody: '', url: location.href };
  try {
    const birthRes = await fetch('https://grok.com/rest/auth/set-birth-date', {
      method: 'POST',
      credentials: 'include',
      headers: {
        'content-type': 'application/json',
        'origin': 'https://grok.com',
        'referer': 'https://grok.com/',
      },
      body: JSON.stringify({ birthDate }),
    });
    out.birthStatus = birthRes.status;
    out.birthBody = (await birthRes.text()).slice(0, 240);
  } catch (e) {
    out.birthBody = String(e);
  }
  const birthOk = (out.birthStatus >= 200 && out.birthStatus < 300)
    || /birth-date-change-limit-reached|Birth date is locked|already set/i.test(out.birthBody || '');
  if (!birthOk && out.birthStatus !== 0) {
    return out;
  }
  try {
    const body = b64ToBytes(nsfwB64);
    const nsfwRes = await fetch('https://grok.com/auth_mgmt.AuthManagement/UpdateUserFeatureControls', {
      method: 'POST',
      credentials: 'include',
      headers: {
        'content-type': 'application/grpc-web+proto',
        'x-grpc-web': '1',
        'origin': 'https://grok.com',
        'referer': 'https://grok.com/',
      },
      body,
    });
    out.nsfwStatus = nsfwRes.status;
    out.nsfwBody = (await nsfwRes.text()).slice(0, 240);
  } catch (e) {
    out.nsfwBody = String(e);
  }
  return out;
})();
            """,
            birth,
            nsfw_b64,
        )
        if not isinstance(result, dict):
            return False, f"浏览器 NSFW 返回异常: {result!r}"

        if log_callback:
            log_callback(
                f"[Debug] browser NSFW birth={result.get('birthStatus')} "
                f"nsfw={result.get('nsfwStatus')} body={str(result.get('birthBody') or '')[:120]}"
            )

        birth_status = int(result.get("birthStatus") or 0)
        birth_body = str(result.get("birthBody") or "")
        birth_ok = (200 <= birth_status < 300) or (
            birth_status in (400, 409, 429)
            and (
                "birth-date-change-limit-reached" in birth_body
                or "Birth date is locked" in birth_body
                or "already set" in birth_body.lower()
            )
        )
        if not birth_ok:
            if "just a moment" in birth_body.lower() or birth_status == 403:
                return False, f"浏览器内 set_birth_date 仍被 CF 拦截 HTTP {birth_status}"
            return False, f"浏览器内 set_birth_date HTTP {birth_status}: {birth_body[:160]}"

        nsfw_status = int(result.get("nsfwStatus") or 0)
        nsfw_body = str(result.get("nsfwBody") or "")
        if 200 <= nsfw_status < 300:
            return True, "成功开启 NSFW（浏览器内）"
        if "just a moment" in nsfw_body.lower() or nsfw_status == 403:
            return False, f"浏览器内 update_nsfw 被 CF 拦截 HTTP {nsfw_status}"
        return False, f"浏览器内 update_nsfw HTTP {nsfw_status}: {nsfw_body[:160]}"
    except Exception as exc:
        if log_callback:
            log_callback(f"[Debug] 浏览器内 NSFW 异常: {exc}")
        return False, f"浏览器内 NSFW 异常: {exc}"


def enable_nsfw_for_token(token, cf_clearance="", user_agent="", log_callback=None):
    proxies = get_proxies()
    ua = user_agent or get_user_agent()
    if log_callback:
        log_callback(
            f"[Debug] NSFW 准备: cf_clearance={'有' if cf_clearance else '无'} | ua_len={len(ua)} | browser={'有' if _active_page() else '无'}"
        )

    # 有活动浏览器时直接走浏览器路径（HTTP 快速路径会被 accounts.x.ai Cloudflare 拦截）
    if _active_page() is not None:
        if log_callback:
            log_callback("[*] NSFW 通过浏览器执行...")
        return enable_nsfw_via_browser(token=token, log_callback=log_callback)

    # 无活动浏览器时尝试 HTTP 快速路径
    def _browser_fallback(reason):
        if _active_page() is None:
            return False, reason
        if log_callback:
            log_callback(f"[*] NSFW HTTP 快速路径未成功: {reason}，回退浏览器过盾...")
        ok, message = enable_nsfw_via_browser(token=token, log_callback=log_callback)
        if ok:
            return True, message
        return False, f"{reason}; browser fallback: {message}"

    try:
        if log_callback:
            log_callback("[*] NSFW 先尝试 HTTP 快速路径...")
        with requests.Session(impersonate="chrome120", proxies=proxies) as session:
            cookie_parts = [f"sso={token}", f"sso-rw={token}"]
            if cf_clearance:
                cookie_parts.append(f"cf_clearance={cf_clearance}")
            session.headers.update(
                {
                    "user-agent": ua,
                    "cookie": "; ".join(cookie_parts),
                    "accept": "application/json, text/plain, */*",
                    "accept-language": "en-US,en;q=0.9",
                }
            )
            ok, message = set_tos_accepted(session, log_callback)
            if not ok:
                return _browser_fallback(message)
            ok, message = set_birth_date(session, log_callback)
            if not ok:
                return _browser_fallback(message)
            ok, message = update_nsfw_settings(session, log_callback)
            if not ok:
                return _browser_fallback(message)
            return True, "成功开启 NSFW（HTTP 快速路径）"
    except Exception as e:
        return _browser_fallback(f"HTTP 快速路径异常: {e}")


# browser session state -> browser_session

def setup_light_theme(root):
    """为桌面 GUI 设置浅色调，并覆盖 Tk/ttk 控件的默认文字颜色。"""
    try:
        root.option_add("*Background", UI_BG)
        root.option_add("*Foreground", UI_FG)
        root.option_add("*selectBackground", UI_ACTIVE_BG)
        root.option_add("*selectForeground", UI_FG)
        root.option_add("*insertBackground", UI_FG)
        root.option_add("*Button.Background", UI_BUTTON_BG)
        root.option_add("*Button.Foreground", UI_FG)
        root.option_add("*Button.activeBackground", UI_ACTIVE_BG)
        root.option_add("*Button.activeForeground", UI_FG)
        root.option_add("*Button.disabledForeground", UI_MUTED_FG)
        root.option_add("*Menubutton.Background", UI_ENTRY_BG)
        root.option_add("*Menubutton.Foreground", UI_FG)
        root.option_add("*Menubutton.activeBackground", UI_ACTIVE_BG)
        root.option_add("*Menubutton.activeForeground", UI_FG)
        root.option_add("*Entry.Background", UI_ENTRY_BG)
        root.option_add("*Text.Background", UI_ENTRY_BG)
        root.option_add("*Menu.Background", UI_ENTRY_BG)
        root.option_add("*Menu.Foreground", UI_FG)
        root.option_add("*Menu.activeBackground", UI_ACTIVE_BG)
        root.option_add("*Menu.activeForeground", UI_FG)
        style = ttk.Style(root)
        available = set(style.theme_names())
        if "clam" in available:
            style.theme_use("clam")
        elif "default" in available:
            style.theme_use("default")
        root.configure(bg=UI_BG)
        style.configure(".", background=UI_BG, foreground=UI_FG, fieldbackground=UI_ENTRY_BG)
        style.configure("TFrame", background=UI_BG)
        style.configure("TLabelframe", background=UI_BG, foreground=UI_FG)
        style.configure("TLabelframe.Label", background=UI_BG, foreground=UI_FG)
        style.configure("TLabel", background=UI_BG, foreground=UI_FG)
        style.configure("TCheckbutton", background=UI_BG, foreground=UI_FG)
        style.configure("TButton", background=UI_BUTTON_BG, foreground=UI_FG)
        style.configure("TEntry", fieldbackground=UI_ENTRY_BG, foreground=UI_FG)
        style.configure("TCombobox", fieldbackground=UI_ENTRY_BG, foreground=UI_FG)
        style.configure("TSpinbox", fieldbackground=UI_ENTRY_BG, foreground=UI_FG)
    except Exception:
        pass


def tk_label(parent, text="", **kwargs):
    return tk.Label(parent, text=text, bg=kwargs.pop("bg", UI_BG), fg=kwargs.pop("fg", UI_FG), **kwargs)


def tk_entry(parent, textvariable=None, width=30, **kwargs):
    """创建带浅色背景和深色文字的文本输入框，供 GUI 配置项复用。"""
    return tk.Entry(
        parent,
        textvariable=textvariable,
        width=width,
        bg=UI_ENTRY_BG,
        fg=UI_FG,
        insertbackground=UI_FG,
        disabledbackground="#eef0f2",
        disabledforeground=UI_MUTED_FG,
        highlightthickness=1,
        highlightbackground="#cbd5e1",
        relief=tk.SOLID,
        **kwargs,
    )


def tk_button(parent, text="", command=None, state=tk.NORMAL, **kwargs):
    """创建带浅色底和深色文字的普通操作按钮，统一处理激活与禁用状态。"""
    return tk.Button(
        parent,
        text=text,
        command=command,
        state=state,
        bg=UI_BUTTON_BG,
        fg=UI_FG,
        activebackground=UI_ACTIVE_BG,
        activeforeground=UI_FG,
        disabledforeground=UI_MUTED_FG,
        relief=tk.RAISED,
        padx=10,
        pady=3,
        **kwargs,
    )


def tk_checkbutton(parent, text="", variable=None, **kwargs):
    """创建浅色界面中的复选框，保持选中状态和文字颜色可辨识。"""
    return tk.Checkbutton(
        parent,
        text=text,
        variable=variable,
        bg=UI_BG,
        fg=UI_FG,
        activebackground=UI_BG,
        activeforeground=UI_FG,
        selectcolor="#3d7be0",
        **kwargs,
    )


def tk_option_menu(parent, variable, values, width=12):
    """创建深色文字的下拉菜单，并同步设置弹出菜单的浅色样式。"""
    menu = tk.OptionMenu(parent, variable, *values)
    menu.configure(
        width=width,
        bg=UI_ENTRY_BG,
        fg=UI_FG,
        activebackground=UI_ACTIVE_BG,
        activeforeground=UI_FG,
        highlightthickness=1,
        highlightbackground="#cbd5e1",
        relief=tk.SOLID,
    )
    menu["menu"].configure(
        bg=UI_ENTRY_BG,
        fg=UI_FG,
        activebackground=UI_ACTIVE_BG,
        activeforeground=UI_FG,
    )
    return menu

def is_debug_mode():
    return bool(config.get("debug_mode", False))


def should_close_browser_after_run(user_stopped: bool) -> bool:
    """正常结束默认关浏览器；用户主动停止时由 close_browser_on_stop 控制。调试模式始终保留。"""
    if is_debug_mode():
        return False
    if user_stopped and not config.get("close_browser_on_stop", False):
        return False
    return True


def maybe_stop_browser(user_stopped: bool = False, log_callback=None):
    if should_close_browser_after_run(user_stopped):
        stop_browser()
        return
    if log_callback and user_stopped:
        log_callback("[*] 用户停止：已保留浏览器（勾选「停止时关闭浏览器」可改为关闭）")


def get_log_level() -> str:
    level = str(config.get("log_level", "info") or "info").strip().lower()
    return level if level in ("info", "debug") else "info"


def should_emit_log(message: str) -> bool:
    """info 级别过滤 [Debug] 行；debug 全开。"""
    if get_log_level() == "debug":
        return True
    text = str(message or "")
    if text.lstrip().startswith("[Debug]") or " [Debug] " in text:
        return False
    return True


def _wire_runtime_modules():
    """把主模块依赖注入到 browser_session / register_flow。"""
    _bs.configure(
        get_proxies=get_proxies,
        is_debug=is_debug_mode,
        extension_path=EXTENSION_PATH,
    )
    _rf.configure(
        get_email_and_token=get_email_and_token,
        get_oai_code=get_oai_code,
        raise_if_cancelled=raise_if_cancelled,
        sleep_with_cancel=sleep_with_cancel,
        RegistrationCancelled=RegistrationCancelled,
        EmailDomainRejected=EmailDomainRejected,
        AccountRetryNeeded=AccountRetryNeeded,
    )

# register page flow -> register_flow

class GrokRegisterGUI:
    """提供邮箱、代理、注册流程和结果统计配置的桌面界面。"""

    def __init__(self, root):
        """初始化主窗口状态并构建全部控件。"""
        self.root = root
        self._ui_thread_id = threading.get_ident()
        self.root.title("Grok 注册机")
        self.root.geometry("1120x900")
        self.root.minsize(960, 700)
        self.is_running = False
        self.batch_count = 0
        self.success_count = 0
        self.fail_count = 0
        self.results = []
        self.stop_requested = False
        # active_task_kind 区分正常注册与独立 SSO 恢复，用于按钮状态和停止日志。
        self.active_task_kind = ""
        self.ui_queue = queue.Queue()
        self.accounts_output_file = ""
        self.setup_ui()
        self.root.after(50, self._drain_ui_queue)

    def _queue_ui_call(self, callback, *args):
        if threading.get_ident() == self._ui_thread_id:
            return False
        self.ui_queue.put((callback, args))
        return True

    def _drain_ui_queue(self):
        while True:
            try:
                callback, args = self.ui_queue.get_nowait()
            except queue.Empty:
                break
            try:
                callback(*args)
            except (tk.TclError, RuntimeError):
                pass
        try:
            self.root.after(50, self._drain_ui_queue)
        except (tk.TclError, RuntimeError):
            pass

    def _on_config_mousewheel(self, event):
        """将配置区鼠标滚轮或触控板事件转换为跨平台 Canvas 滚动。"""
        try:
            canvas = self.config_canvas
            # macOS 的 MouseWheel 事件中 num 可能是“??”，不能直接强制转成整数。
            event_number = str(getattr(event, "num", "") or "").strip()
            if event_number == "4":
                units = -1
            elif event_number == "5":
                units = 1
            else:
                delta = float(getattr(event, "delta", 0) or 0)
                if delta == 0:
                    return None
                # Windows 常以 120 为一格；macOS 触控板通常连续发送较小 delta。
                magnitude = (
                    round(abs(delta) / 120)
                    if abs(delta) >= 120
                    else round(abs(delta))
                )
                magnitude = max(1, min(4, int(magnitude)))
                units = -magnitude if delta > 0 else magnitude

            scroll_region = canvas.bbox("all")
            if (
                scroll_region is None
                or scroll_region[3] - scroll_region[1]
                <= canvas.winfo_height()
            ):
                return None
            canvas.yview_scroll(units, "units")
            return "break"
        except (tk.TclError, ValueError, TypeError):
            return None

    def _bind_config_mousewheel_tree(self, widget):
        """为配置视口及其全部子控件安装优先于控件默认行为的滚轮标签。"""
        bindtag = self._config_mousewheel_bindtag
        bindtags = tuple(widget.bindtags())
        if bindtag not in bindtags:
            widget.bindtags((bindtag, *bindtags))
        for child in widget.winfo_children():
            self._bind_config_mousewheel_tree(child)

    def _on_config_content_resize(self, _event=None):
        """在配置字段显隐或尺寸变化后刷新 Canvas 的纵向滚动范围。"""
        try:
            scroll_region = self.config_canvas.bbox("all")
            if scroll_region is not None:
                self.config_canvas.configure(scrollregion=scroll_region)
                if (
                    scroll_region[3] - scroll_region[1]
                    <= self.config_canvas.winfo_height()
                ):
                    self.config_canvas.yview_moveto(0)
        except tk.TclError:
            pass

    def _on_config_canvas_resize(self, event):
        """让 Canvas 内部配置面板始终铺满可见宽度，避免出现横向滚动。"""
        try:
            self.config_canvas.itemconfigure(
                self._config_canvas_window,
                width=max(int(event.width), 1),
            )
            self._on_config_content_resize()
        except (tk.TclError, ValueError, TypeError):
            pass

    def setup_ui(self):
        """构建带滚动配置视口的主界面，并按邮箱 provider 切换专属字段。"""
        load_config()
        _wire_runtime_modules()
        main_frame = tk.Frame(self.root, bg=UI_BG, padx=10, pady=10)
        main_frame.pack(fill=tk.BOTH, expand=True)
        main_frame.grid_columnconfigure(0, weight=1)
        main_frame.grid_rowconfigure(0, weight=3, minsize=280)
        main_frame.grid_rowconfigure(3, weight=2, minsize=180)

        config_scroll_host = tk.Frame(main_frame, bg=UI_BG)
        config_scroll_host.grid(
            row=0,
            column=0,
            sticky=tk.NSEW,
            pady=(0, 8),
        )
        config_scroll_host.grid_columnconfigure(0, weight=1)
        config_scroll_host.grid_rowconfigure(0, weight=1)
        # config_canvas 限制配置区的请求高度，让底部日志始终获得可见空间。
        self.config_canvas = tk.Canvas(
            config_scroll_host,
            bg=UI_PANEL_BG,
            highlightthickness=0,
            borderwidth=0,
            height=400,
        )
        self.config_canvas.grid(row=0, column=0, sticky=tk.NSEW)
        # config_scrollbar 只控制上方配置视口，不影响日志框自己的滚动条。
        self.config_scrollbar = ttk.Scrollbar(
            config_scroll_host,
            orient=tk.VERTICAL,
            command=self.config_canvas.yview,
        )
        self.config_scrollbar.grid(row=0, column=1, sticky=tk.NS)
        self.config_canvas.configure(
            yscrollcommand=self.config_scrollbar.set,
        )
        config_frame = tk.LabelFrame(
            self.config_canvas,
            text="配置",
            bg=UI_PANEL_BG,
            fg=UI_FG,
            padx=10,
            pady=10,
            relief=tk.GROOVE,
            borderwidth=1,
        )
        # _config_canvas_window 保存内部面板的 Canvas item，窗口缩放时同步宽度。
        self._config_canvas_window = self.config_canvas.create_window(
            (0, 0),
            window=config_frame,
            anchor=tk.NW,
        )
        config_frame.grid_columnconfigure(1, weight=1, minsize=260)
        config_frame.grid_columnconfigure(3, weight=1, minsize=260)
        config_frame.bind("<Configure>", self._on_config_content_resize)
        self.config_canvas.bind("<Configure>", self._on_config_canvas_resize)
        # _config_mousewheel_bindtag 只拦截配置区事件，并放在默认控件绑定之前。
        self._config_mousewheel_bindtag = f"ConfigMouseWheel-{id(self)}"
        self.root.bind_class(
            self._config_mousewheel_bindtag,
            "<MouseWheel>",
            self._on_config_mousewheel,
        )
        self.root.bind_class(
            self._config_mousewheel_bindtag,
            "<Button-4>",
            self._on_config_mousewheel,
        )
        self.root.bind_class(
            self._config_mousewheel_bindtag,
            "<Button-5>",
            self._on_config_mousewheel,
        )

        def add_label(row, column, text):
            tk_label(config_frame, text=text, bg=UI_PANEL_BG).grid(
                row=row,
                column=column,
                sticky=tk.W,
                padx=(0, 6),
                pady=3,
            )

        def add_field(widget, row, column, columnspan=1, sticky=tk.EW):
            widget.grid(
                row=row,
                column=column,
                columnspan=columnspan,
                sticky=sticky,
                padx=(0, 14),
                pady=3,
            )

        # 公共配置
        add_label(1, 0, "邮箱服务商:")
        self.email_provider_var = tk.StringVar(value=config.get("email_provider", "cloudflare"))
        self.email_provider_combo = tk_option_menu(
            config_frame,
            self.email_provider_var,
            [
                "outlook_email",
                "icloud",
                "duckmail",
                "yyds",
                "cloudflare",
                "mailnest",
                "cloudmail",
            ],
            width=12,
        )
        add_field(self.email_provider_combo, 1, 1, sticky=tk.W)

        add_label(0, 0, "注册选项:")
        # opt_frame 集中展示调试项及整批注册的数量、并发和账号间隔。
        opt_frame = tk.Frame(config_frame, bg=UI_PANEL_BG)
        add_field(opt_frame, 0, 1, columnspan=3, sticky=tk.EW)
        # debug_mode_var 控制单账号调试模式，启用时强制数量和并发均为一。
        self.debug_mode_var = tk.BooleanVar(value=bool(config.get("debug_mode", False)))
        # debug_mode_check 允许在 GUI 顶部快速切换调试运行方式。
        self.debug_mode_check = tk_checkbutton(
            opt_frame, text="调试模式（可选）", variable=self.debug_mode_var
        )
        self.debug_mode_check.pack(side=tk.LEFT)
        # log_level_var 保存当前批次的日志详细程度。
        self.log_level_var = tk.StringVar(value=str(config.get("log_level", "info") or "info"))
        tk_label(opt_frame, text="日志:", bg=UI_PANEL_BG).pack(side=tk.LEFT, padx=(12, 2))
        # log_level_combo 提供 info 与 debug 两种日志等级。
        self.log_level_combo = tk_option_menu(opt_frame, self.log_level_var, ["info", "debug"], width=6)
        self.log_level_combo.pack(side=tk.LEFT)
        tk_label(opt_frame, text="注册数量:", bg=UI_PANEL_BG).pack(
            side=tk.LEFT,
            padx=(14, 4),
        )
        # count_var 保存本批次需要完成的账号总数。
        self.count_var = tk.StringVar(value=str(config.get("register_count", 1)))
        # count_spinbox 限制 GUI 单批次注册数量的输入范围。
        self.count_spinbox = tk.Spinbox(
            opt_frame,
            from_=1,
            to=2500,
            width=6,
            textvariable=self.count_var,
            bg=UI_ENTRY_BG,
            fg=UI_FG,
            insertbackground=UI_FG,
            buttonbackground=UI_BUTTON_BG,
            disabledbackground="#2f2f2f",
            disabledforeground=UI_MUTED_FG,
            relief=tk.SOLID,
        )
        self.count_spinbox.pack(side=tk.LEFT)
        tk_label(opt_frame, text="并发数:", bg=UI_PANEL_BG).pack(
            side=tk.LEFT,
            padx=(14, 4),
        )
        # workers_var 保存完整账号流程并行运行的 worker 数量。
        self.workers_var = tk.StringVar(value=str(config.get("register_workers", 1)))
        # workers_spinbox 将 GUI 并发输入限制在浏览器工作线程的安全范围内。
        self.workers_spinbox = tk.Spinbox(
            opt_frame,
            from_=1,
            to=8,
            width=5,
            textvariable=self.workers_var,
            bg=UI_ENTRY_BG,
            fg=UI_FG,
            insertbackground=UI_FG,
            buttonbackground=UI_BUTTON_BG,
            disabledbackground="#2f2f2f",
            disabledforeground=UI_MUTED_FG,
            relief=tk.SOLID,
        )
        self.workers_spinbox.pack(side=tk.LEFT)
        tk_label(opt_frame, text="账号间隔（秒）:", bg=UI_PANEL_BG).pack(
            side=tk.LEFT,
            padx=(14, 4),
        )
        # account_interval_var 保存每个 worker 完成一轮后等待的固定值或随机区间。
        self.account_interval_var = tk.StringVar(
            value=str(config.get("account_interval", "60-120") or "60-120")
        )
        # account_interval_entry 接收整数或“最小值-最大值”格式的等待秒数。
        self.account_interval_entry = tk_entry(
            opt_frame,
            textvariable=self.account_interval_var,
            width=11,
        )
        self.account_interval_entry.pack(side=tk.LEFT)

        # proxy_var 保存普通代理与 Resin 共用的代理入口地址。
        self.proxy_var = tk.StringVar(value=config.get("proxy", ""))

        add_label(3, 0, "代理类型:")
        # proxy_mode_var 保存 GUI 展示值，写入配置时转换为 normal/resin。
        self.proxy_mode_var = tk.StringVar(
            value=(
                "Resin 粘性代理"
                if is_resin_proxy_mode(config)
                else "普通代理"
            )
        )
        # proxy_mode_combo 允许在原有普通代理和 Resin 粘性代理之间切换。
        self.proxy_mode_combo = tk_option_menu(
            config_frame,
            self.proxy_mode_var,
            ["普通代理", "Resin 粘性代理"],
            width=16,
        )
        add_field(self.proxy_mode_combo, 3, 1, sticky=tk.W)

        # proxy_details_frame 承载当前代理模式对应的地址、认证及隧道输入项。
        self.proxy_details_frame = tk.LabelFrame(
            config_frame,
            text="代理配置",
            bg=UI_PANEL_BG,
            fg=UI_FG,
            padx=8,
            pady=6,
            relief=tk.GROOVE,
            borderwidth=1,
        )
        self.proxy_details_frame.grid(
            row=4,
            column=0,
            columnspan=4,
            sticky=tk.EW,
            pady=(6, 4),
        )
        self.proxy_details_frame.grid_columnconfigure(1, weight=1, minsize=240)
        self.proxy_details_frame.grid_columnconfigure(3, weight=1, minsize=240)
        tk_label(
            self.proxy_details_frame,
            text="代理地址（可选）:",
            bg=UI_PANEL_BG,
        ).grid(row=0, column=0, sticky=tk.W, padx=(0, 6), pady=3)
        # proxy_entry 允许普通代理和 Resin 复用同一个入口地址配置。
        self.proxy_entry = tk_entry(
            self.proxy_details_frame,
            textvariable=self.proxy_var,
            width=52,
        )
        self.proxy_entry.grid(
            row=0,
            column=1,
            columnspan=3,
            sticky=tk.EW,
            padx=(0, 14),
            pady=3,
        )

        # resin_frame 仅在 Resin 模式显示 Token、平台和可选 SSH 配置。
        self.resin_frame = tk.Frame(self.proxy_details_frame, bg=UI_PANEL_BG)
        self.resin_frame.grid(
            row=1,
            column=0,
            columnspan=4,
            sticky=tk.EW,
            padx=(0, 14),
            pady=3,
        )
        self.resin_frame.grid_columnconfigure(1, weight=1)
        self.resin_frame.grid_columnconfigure(3, weight=1)
        # resin_token_var 保存 Resin 正向代理密码，输入控件始终以掩码显示。
        self.resin_token_var = tk.StringVar(
            value=str(config.get("resin_token", "") or "")
        )
        # resin_platform_var 保存 Resin 节点隔离平台，默认使用全部节点平台。
        self.resin_platform_var = tk.StringVar(
            value=str(
                config.get("resin_platform", RESIN_DEFAULT_PLATFORM)
                or RESIN_DEFAULT_PLATFORM
            )
        )
        # resin_enable_tunnel_var 控制是否自动管理 Resin 专属 SSH 子进程。
        self.resin_enable_tunnel_var = tk.BooleanVar(
            value=bool(config.get("resin_enable_tunnel", False))
        )
        # resin_ssh_key_var 保存 Resin 隧道私钥；首次迁移可沿用 iCloud 私钥。
        self.resin_ssh_key_var = tk.StringVar(
            value=str(
                config.get("resin_ssh_key", "")
                or config.get("icloud_ssh_key", "")
                or "~/.ssh/MaXiangLinTxCloudMiYao.pem"
            )
        )
        # resin_ssh_user_var 保存部署 Resin 的云服务器登录用户。
        self.resin_ssh_user_var = tk.StringVar(
            value=str(
                config.get("resin_ssh_user", "")
                or config.get("icloud_ssh_user", "")
                or "ubuntu"
            )
        )
        # resin_ssh_host_var 保存 Resin 部署服务器，不依赖当前邮箱服务商。
        self.resin_ssh_host_var = tk.StringVar(
            value=str(
                config.get("resin_ssh_host", "")
                or config.get("icloud_ssh_host", "")
                or ""
            )
        )
        # resin_local_port_var 保存本机 Resin 隧道入口端口，默认使用 12260。
        self.resin_local_port_var = tk.StringVar(
            value=str(config.get("resin_local_port", 12260) or 12260)
        )
        # resin_remote_port_var 保存服务器回环地址上的 Resin 端口。
        self.resin_remote_port_var = tk.StringVar(
            value=str(config.get("resin_remote_port", 2260) or 2260)
        )
        # resin_tunnel_check 控制 Resin SSH 配置区是否显示及是否自动管理隧道。
        self.resin_tunnel_check = tk_checkbutton(
            config_frame,
            text="是否需要自动建立或复用 SSH 通道",
            variable=self.resin_enable_tunnel_var,
        )
        self.resin_tunnel_check.grid(
            row=3,
            column=2,
            columnspan=2,
            sticky=tk.W,
            padx=(0, 14),
            pady=3,
        )
        tk_label(self.resin_frame, text="Resin Token:", bg=UI_PANEL_BG).grid(
            row=0,
            column=0,
            sticky=tk.W,
            padx=(0, 6),
        )
        # resin_token_entry 以密码掩码接收 Token，防止 GUI 截图直接暴露凭据。
        self.resin_token_entry = tk_entry(
            self.resin_frame,
            textvariable=self.resin_token_var,
            width=24,
            show="*",
        )
        self.resin_token_entry.grid(
            row=0,
            column=1,
            sticky=tk.EW,
            padx=(0, 14),
        )
        tk_label(self.resin_frame, text="Platform:", bg=UI_PANEL_BG).grid(
            row=0,
            column=2,
            sticky=tk.W,
            padx=(0, 6),
        )
        # resin_platform_entry 允许选择 Default 或 Resin 中已创建的自定义平台。
        self.resin_platform_entry = tk_entry(
            self.resin_frame,
            textvariable=self.resin_platform_var,
            width=18,
        )
        self.resin_platform_entry.grid(row=0, column=3, sticky=tk.EW)

        # resin_ssh_frame 仅在 Resin 模式且启用 SSH 通道时显示连接参数。
        self.resin_ssh_frame = tk.Frame(self.resin_frame, bg=UI_PANEL_BG)
        self.resin_ssh_frame.grid(
            row=1,
            column=0,
            columnspan=4,
            sticky=tk.EW,
            pady=(4, 0),
        )
        self.resin_ssh_frame.grid_columnconfigure(1, weight=1)
        self.resin_ssh_frame.grid_columnconfigure(3, weight=1)
        tk_label(self.resin_ssh_frame, text="SSH 主机:", bg=UI_PANEL_BG).grid(
            row=0,
            column=0,
            sticky=tk.W,
            padx=(0, 6),
        )
        tk_entry(
            self.resin_ssh_frame,
            textvariable=self.resin_ssh_host_var,
            width=24,
        ).grid(
            row=0,
            column=1,
            sticky=tk.EW,
            padx=(0, 14),
        )
        tk_label(self.resin_ssh_frame, text="SSH 用户:", bg=UI_PANEL_BG).grid(
            row=0,
            column=2,
            sticky=tk.W,
            padx=(0, 6),
        )
        tk_entry(
            self.resin_ssh_frame,
            textvariable=self.resin_ssh_user_var,
            width=18,
        ).grid(
            row=0,
            column=3,
            sticky=tk.EW,
        )
        tk_label(self.resin_ssh_frame, text="SSH 私钥:", bg=UI_PANEL_BG).grid(
            row=1,
            column=0,
            sticky=tk.W,
            padx=(0, 6),
            pady=(4, 0),
        )
        tk_entry(
            self.resin_ssh_frame,
            textvariable=self.resin_ssh_key_var,
            width=52,
        ).grid(
            row=1,
            column=1,
            columnspan=3,
            sticky=tk.EW,
            pady=(4, 0),
        )
        tk_label(self.resin_ssh_frame, text="本地端口:", bg=UI_PANEL_BG).grid(
            row=2,
            column=0,
            sticky=tk.W,
            padx=(0, 6),
            pady=(4, 0),
        )
        tk_entry(
            self.resin_ssh_frame,
            textvariable=self.resin_local_port_var,
            width=12,
        ).grid(
            row=2,
            column=1,
            sticky=tk.W,
            padx=(0, 14),
            pady=(4, 0),
        )
        tk_label(self.resin_ssh_frame, text="远端端口:", bg=UI_PANEL_BG).grid(
            row=2,
            column=2,
            sticky=tk.W,
            padx=(0, 6),
            pady=(4, 0),
        )
        tk_entry(
            self.resin_ssh_frame,
            textvariable=self.resin_remote_port_var,
            width=12,
        ).grid(
            row=2,
            column=3,
            sticky=tk.W,
            pady=(4, 0),
        )

        # 服务商专属配置（按选择显示）
        self.provider_frame = tk.LabelFrame(
            config_frame,
            text="邮箱服务商配置",
            bg=UI_PANEL_BG,
            fg=UI_FG,
            padx=8,
            pady=6,
            relief=tk.GROOVE,
            borderwidth=1,
        )
        self.provider_frame.grid(row=2, column=0, columnspan=4, sticky=tk.EW, pady=(6, 4))
        self.provider_frame.grid_columnconfigure(1, weight=1, minsize=240)
        self.provider_frame.grid_columnconfigure(3, weight=1, minsize=240)

        def p_label(row, column, text):
            w = tk_label(self.provider_frame, text=text, bg=UI_PANEL_BG)
            w.grid(row=row, column=column, sticky=tk.W, padx=(0, 6), pady=3)
            return w

        def p_field(widget, row, column, columnspan=1, sticky=tk.EW):
            widget.grid(
                row=row,
                column=column,
                columnspan=columnspan,
                sticky=sticky,
                padx=(0, 14),
                pady=3,
            )
            return widget

        # DuckMail / Mail.tm
        self.api_key_var = tk.StringVar(value=config.get("duckmail_api_key", ""))
        self.duckmail_api_base_var = tk.StringVar(
            value=str(config.get("duckmail_api_base", "") or DUCKMAIL_API_BASE_DEFAULT)
        )
        self._duckmail_widgets = [
            p_label(0, 0, "API Base（可选）:"),
            p_field(tk_entry(self.provider_frame, textvariable=self.duckmail_api_base_var, width=52), 0, 1, columnspan=3),
            p_label(1, 0, "API Key（可选）:"),
            p_field(tk_entry(self.provider_frame, textvariable=self.api_key_var, width=34), 1, 1),
            p_label(1, 2, "说明:"),
            p_field(
                tk_label(
                    self.provider_frame,
                    text="Mail.tm 填 https://api.mail.tm；公共域可不填 Key",
                    bg=UI_PANEL_BG,
                ),
                1,
                3,
                sticky=tk.W,
            ),
        ]

        # Cloudflare
        self.cloudflare_auth_mode_var = tk.StringVar(value=config.get("cloudflare_auth_mode", "none"))
        self.cloudflare_api_base_var = tk.StringVar(value=config.get("cloudflare_api_base", ""))
        self.cloudflare_api_key_var = tk.StringVar(value=config.get("cloudflare_api_key", ""))
        self.cloudflare_paths_var = tk.StringVar(
            value=",".join(
                [
                    config.get("cloudflare_path_domains", "/api/domains"),
                    config.get("cloudflare_path_accounts", "/api/new_address"),
                    config.get("cloudflare_path_token", "/api/token"),
                    config.get("cloudflare_path_messages", "/api/mails"),
                ]
            )
        )
        self.default_domains_var = tk.StringVar(value=str(config.get("defaultDomains", "")))
        self.cloudflare_custom_auth_var = tk.StringVar(value=str(config.get("cloudflare_custom_auth", "")))
        self._cloudflare_widgets = [
            p_label(0, 0, "API Base:"),
            p_field(tk_entry(self.provider_frame, textvariable=self.cloudflare_api_base_var, width=52), 0, 1, columnspan=3),
            p_label(1, 0, "鉴权模式（可选）:"),
            p_field(
                tk_option_menu(
                    self.provider_frame,
                    self.cloudflare_auth_mode_var,
                    ["query-key", "bearer", "x-api-key", "x-admin-auth", "none"],
                    width=12,
                ),
                1,
                1,
                sticky=tk.W,
            ),
            p_label(1, 2, "API Key（可选）:"),
            p_field(tk_entry(self.provider_frame, textvariable=self.cloudflare_api_key_var, width=34), 1, 3),
            p_label(2, 0, "收信域名（可选）:"),
            p_field(tk_entry(self.provider_frame, textvariable=self.default_domains_var, width=34), 2, 1),
            p_label(2, 2, "全局密码（可选）:"),
            p_field(tk_entry(self.provider_frame, textvariable=self.cloudflare_custom_auth_var, width=34), 2, 3),
            p_label(3, 0, "CF 路径（可选）:"),
            p_field(tk_entry(self.provider_frame, textvariable=self.cloudflare_paths_var, width=52), 3, 1, columnspan=3),
        ]

        # YYDS
        self.yyds_api_key_var = tk.StringVar(value=str(config.get("yyds_api_key", "")))
        self.yyds_jwt_var = tk.StringVar(value=str(config.get("yyds_jwt", "")))
        self.yyds_default_domain_var = tk.StringVar(value=str(config.get("yyds_default_domain", "")))
        self._yyds_widgets = [
            p_label(0, 0, "API Key（可选）:"),
            p_field(tk_entry(self.provider_frame, textvariable=self.yyds_api_key_var, width=34), 0, 1),
            p_label(0, 2, "JWT（可选）:"),
            p_field(tk_entry(self.provider_frame, textvariable=self.yyds_jwt_var, width=34), 0, 3),
            p_label(1, 0, "固定收信域名（可选）:"),
            p_field(tk_entry(self.provider_frame, textvariable=self.yyds_default_domain_var, width=34), 1, 1),
            p_label(1, 2, "说明:"),
            p_field(
                tk_label(self.provider_frame, text="Key/JWT 二选一；域名留空则自动选", bg=UI_PANEL_BG),
                1,
                3,
                sticky=tk.W,
            ),
        ]

        # MailNest
        self.mailnest_api_key_var = tk.StringVar(value=str(config.get("mailnest_api_key", "")))
        self.mailnest_project_code_var = tk.StringVar(
            value=str(config.get("mailnest_project_code", MAILNEST_DEFAULT_PROJECT_CODE) or MAILNEST_DEFAULT_PROJECT_CODE)
        )
        self._mailnest_widgets = [
            p_label(0, 0, "API Key:"),
            p_field(tk_entry(self.provider_frame, textvariable=self.mailnest_api_key_var, width=34), 0, 1),
            p_label(0, 2, "项目代码（可选）:"),
            p_field(tk_entry(self.provider_frame, textvariable=self.mailnest_project_code_var, width=34), 0, 3),
        ]

        # CloudMail
        self.cloudmail_url_var = tk.StringVar(value=str(config.get("cloudmail_url", "")))
        self.cloudmail_admin_email_var = tk.StringVar(value=str(config.get("cloudmail_admin_email", "")))
        self.cloudmail_password_var = tk.StringVar(value=str(config.get("cloudmail_password", "")))
        # CloudMail 也用 defaultDomains；与 CF 共用变量即可
        self._cloudmail_widgets = [
            p_label(0, 0, "站点 URL:"),
            p_field(tk_entry(self.provider_frame, textvariable=self.cloudmail_url_var, width=52), 0, 1, columnspan=3),
            p_label(1, 0, "管理员邮箱:"),
            p_field(tk_entry(self.provider_frame, textvariable=self.cloudmail_admin_email_var, width=34), 1, 1),
            p_label(1, 2, "管理员密码:"),
            p_field(
                tk_entry(self.provider_frame, textvariable=self.cloudmail_password_var, width=34, show="*"),
                1,
                3,
            ),
            p_label(2, 0, "收信域名:"),
            p_field(tk_entry(self.provider_frame, textvariable=self.default_domains_var, width=34), 2, 1),
            p_label(2, 2, "说明:"),
            p_field(
                tk_label(self.provider_frame, text="多个域名用逗号分隔", bg=UI_PANEL_BG),
                2,
                3,
                sticky=tk.W,
            ),
        ]

        # OutlookEmail 完整 API
        # outlook_email_base_url_var 保存部署站点地址，不复用注册代理。
        self.outlook_email_base_url_var = tk.StringVar(
            value=str(config.get("outlook_email_base_url", "") or "")
        )
        # outlook_email_login_password_var 保存 Web 登录密码并始终以掩码显示。
        self.outlook_email_login_password_var = tk.StringVar(
            value=str(config.get("outlook_email_login_password", "") or "")
        )
        # outlook_email_project_key_var 保存跨 worker 共用的项目唯一标识。
        self.outlook_email_project_key_var = tk.StringVar(
            value=str(
                config.get("outlook_email_project_key", "grok-register")
                or "grok-register"
            )
        )
        outlook_group_ids = config.get("outlook_email_group_ids", []) or []
        outlook_group_ids_text = (
            str(outlook_group_ids)
            if isinstance(outlook_group_ids, str)
            else ",".join(str(item) for item in outlook_group_ids)
        )
        # outlook_email_group_ids_var 接收可选的逗号分隔分组 ID，留空表示全部普通邮箱。
        self.outlook_email_group_ids_var = tk.StringVar(
            value=outlook_group_ids_text
        )
        # outlook_email_use_alias_email_var 控制项目是否优先领取账号别名。
        self.outlook_email_use_alias_email_var = tk.BooleanVar(
            value=bool(config.get("outlook_email_use_alias_email", False))
        )
        # OutlookEmail 专属控件集合用于 provider 切换时整体显示或隐藏。
        self._outlook_email_widgets = [
            p_label(0, 0, "服务地址:"),
            p_field(
                tk_entry(
                    self.provider_frame,
                    textvariable=self.outlook_email_base_url_var,
                    width=52,
                ),
                0,
                1,
                columnspan=3,
            ),
            p_label(1, 0, "Web 登录密码:"),
            p_field(
                tk_entry(
                    self.provider_frame,
                    textvariable=self.outlook_email_login_password_var,
                    width=34,
                    show="*",
                ),
                1,
                1,
            ),
            p_label(1, 2, "项目标识:"),
            p_field(
                tk_entry(
                    self.provider_frame,
                    textvariable=self.outlook_email_project_key_var,
                    width=34,
                ),
                1,
                3,
            ),
            p_label(2, 0, "分组 ID（可选）:"),
            p_field(
                tk_entry(
                    self.provider_frame,
                    textvariable=self.outlook_email_group_ids_var,
                    width=34,
                ),
                2,
                1,
            ),
            p_label(2, 2, "领取方式:"),
            p_field(
                tk_checkbutton(
                    self.provider_frame,
                    text="优先使用账号别名",
                    variable=self.outlook_email_use_alias_email_var,
                ),
                2,
                3,
                sticky=tk.W,
            ),
            p_label(3, 0, "说明:"),
            p_field(
                tk_label(
                    self.provider_frame,
                    text="留空分组 ID 即使用全部普通邮箱；无需配置对外 API Key",
                    bg=UI_PANEL_BG,
                ),
                3,
                1,
                columnspan=3,
                sticky=tk.W,
            ),
        ]

        # iCloud HME
        # 本地 API 地址始终指向 SSH 隧道监听端口。
        self.icloud_api_base_var = tk.StringVar(
            value=str(
                config.get("icloud_api_base", "http://127.0.0.1:18090")
                or "http://127.0.0.1:18090"
            )
        )
        # 自动隧道开关控制注册机是否自行管理 SSH 子进程。
        self.icloud_enable_tunnel_var = tk.BooleanVar(
            value=bool(config.get("icloud_enable_tunnel", True))
        )
        # SSH 私钥路径仅用于本机端口转发，不承载 iCloud 凭据。
        self.icloud_ssh_key_var = tk.StringVar(
            value=str(
                config.get(
                    "icloud_ssh_key", "~/.ssh/MaXiangLinTxCloudMiYao.pem"
                )
                or "~/.ssh/MaXiangLinTxCloudMiYao.pem"
            )
        )
        # SSH 用户对应云服务器系统登录账号。
        self.icloud_ssh_user_var = tk.StringVar(
            value=str(config.get("icloud_ssh_user", "ubuntu") or "ubuntu")
        )
        # SSH 主机对应仅通过密钥访问的 icloud-hme 云服务器。
        self.icloud_ssh_host_var = tk.StringVar(
            value=str(config.get("icloud_ssh_host", "") or "")
        )
        # 本地端口与 API Base 中的监听端口保持一致。
        self.icloud_local_port_var = tk.StringVar(
            value=str(config.get("icloud_local_port", 18090) or 18090)
        )
        # 远端端口对应云服务器回环地址上的 icloud-hme 服务。
        self.icloud_remote_port_var = tk.StringVar(
            value=str(config.get("icloud_remote_port", 8090) or 8090)
        )
        # iCloud 专属控件集合用于切换 provider 时统一显示或隐藏。
        self._icloud_widgets = [
            p_label(0, 0, "API Base:"),
            p_field(
                tk_entry(
                    self.provider_frame,
                    textvariable=self.icloud_api_base_var,
                    width=52,
                ),
                0,
                1,
                columnspan=3,
            ),
            p_label(1, 0, "SSH 主机:"),
            p_field(
                tk_entry(
                    self.provider_frame,
                    textvariable=self.icloud_ssh_host_var,
                    width=34,
                ),
                1,
                1,
            ),
            p_label(1, 2, "SSH 用户:"),
            p_field(
                tk_entry(
                    self.provider_frame,
                    textvariable=self.icloud_ssh_user_var,
                    width=34,
                ),
                1,
                3,
            ),
            p_label(2, 0, "SSH 私钥:"),
            p_field(
                tk_entry(
                    self.provider_frame,
                    textvariable=self.icloud_ssh_key_var,
                    width=52,
                ),
                2,
                1,
                columnspan=3,
            ),
            p_label(3, 0, "本地端口:"),
            p_field(
                tk_entry(
                    self.provider_frame,
                    textvariable=self.icloud_local_port_var,
                    width=16,
                ),
                3,
                1,
                sticky=tk.W,
            ),
            p_label(3, 2, "远端端口:"),
            p_field(
                tk_entry(
                    self.provider_frame,
                    textvariable=self.icloud_remote_port_var,
                    width=16,
                ),
                3,
                3,
                sticky=tk.W,
            ),
            p_label(4, 0, "隧道:"),
            p_field(
                tk_checkbutton(
                    self.provider_frame,
                    text="自动建立或复用 SSH 隧道",
                    variable=self.icloud_enable_tunnel_var,
                ),
                4,
                1,
                columnspan=3,
                sticky=tk.W,
            ),
        ]

        # provider 控件映射保证界面只显示当前邮箱后端的配置字段。
        self._provider_widget_groups = {
            "outlook_email": self._outlook_email_widgets,
            "icloud": self._icloud_widgets,
            "duckmail": self._duckmail_widgets,
            "cloudflare": self._cloudflare_widgets,
            "yyds": self._yyds_widgets,
            "mailnest": self._mailnest_widgets,
            "cloudmail": self._cloudmail_widgets,
        }

        # SSO → CPA auth 可选
        self.cpa_frame = tk.LabelFrame(
            config_frame,
            text="SSO → auth 输出（可选）",
            bg=UI_PANEL_BG,
            fg=UI_FG,
            padx=8,
            pady=6,
            relief=tk.GROOVE,
            borderwidth=1,
        )
        self.cpa_frame.grid(row=5, column=0, columnspan=4, sticky=tk.EW, pady=(6, 2))
        self.cpa_frame.grid_columnconfigure(1, weight=1, minsize=240)
        self.cpa_frame.grid_columnconfigure(3, weight=1, minsize=240)

        # 总开关决定注册成功后是否执行 SSO 换 token 与后续凭据交付。
        self.cpa_auto_add_var = tk.BooleanVar(value=bool(config.get("cpa_auto_add", False)))
        tk_checkbutton(
            self.cpa_frame,
            text="开启后注册成功：SSO 换 token，写入 CPA / Grok2API（不勾选则只保存 SSO）",
            variable=self.cpa_auto_add_var,
        ).grid(row=0, column=0, columnspan=4, sticky=tk.W, pady=3)

        # 详情控件集合用于总开关关闭时统一隐藏高级配置。
        self._cpa_detail_widgets = []

        def c_label(row, col, text):
            """创建并登记 SSO→auth 配置区的文本标签。"""
            w = tk_label(self.cpa_frame, text=text, bg=UI_PANEL_BG)
            w.grid(row=row, column=col, sticky=tk.W, padx=(0, 6), pady=3)
            self._cpa_detail_widgets.append(w)
            return w

        def c_field(widget, row, col, columnspan=1, sticky=tk.EW):
            """布置并登记 SSO→auth 配置区的输入控件。"""
            widget.grid(row=row, column=col, columnspan=columnspan, sticky=sticky, padx=(0, 14), pady=3)
            self._cpa_detail_widgets.append(widget)
            return widget

        # Token 换取方式选择
        _cur_mode = str(config.get("cpa_token_mode", "device_protocol") or "device_protocol")
        _mode_display = {
            "device_protocol": "协议 Device Flow",
            "device_browser": "浏览器 Device Flow",
            "auth_code": "Authorization Code",
        }.get(_cur_mode, "协议 Device Flow")
        self.cpa_token_mode_var = tk.StringVar(value=_mode_display)
        c_label(1, 0, "Token 换取:")
        token_mode_menu = tk_option_menu(
            self.cpa_frame,
            self.cpa_token_mode_var,
            ["协议 Device Flow", "浏览器 Device Flow", "Authorization Code"],
            width=20,
        )
        c_field(token_mode_menu, 1, 1)

        # 两个输出目标可独立启停，默认同时交付 CPA 与 Grok2API。
        self.cpa_enabled_var = tk.BooleanVar(value=bool(config.get("cpa_enabled", True)))
        self.grok2api_enabled_var = tk.BooleanVar(
            value=bool(config.get("grok2api_enabled", True))
        )
        c_label(1, 2, "输出目标:")
        output_target_frame = tk.Frame(self.cpa_frame, bg=UI_PANEL_BG)
        tk_checkbutton(
            output_target_frame,
            text="CPA",
            variable=self.cpa_enabled_var,
        ).pack(side=tk.LEFT, padx=(0, 12))
        tk_checkbutton(
            output_target_frame,
            text="Grok2API",
            variable=self.grok2api_enabled_var,
        ).pack(side=tk.LEFT)
        c_field(output_target_frame, 1, 3, sticky=tk.W)

        # CPA 本地目录仅在远程交付最终失败时保存 auth 兜底文件。
        self.cpa_auth_dir_var = tk.StringVar(value=str(config.get("cpa_auth_dir", "")))
        # CPA 服务器地址指向 CLIProxyAPI Management API 所在实例。
        self.cpa_remote_url_var = tk.StringVar(value=str(config.get("cpa_remote_url", "")))
        # CPA 管理密钥用于 Bearer 鉴权，日志和输入框均不会明文展示。
        self.cpa_management_key_var = tk.StringVar(value=str(config.get("cpa_management_key", "")))
        # Grok2API 本地目录分别承接 Web 与 Build 远程失败后的备用文件。
        self.grok2api_auth_dir_var = tk.StringVar(value=str(config.get("grok2api_auth_dir", "")))
        # Grok2API 服务器地址作为管理员登录及两个导入接口的共同基础地址。
        self.grok2api_remote_url_var = tk.StringVar(
            value=str(config.get("grok2api_remote_url", ""))
        )
        # Grok2API 管理员用户名用于换取远程导入所需的短期访问令牌。
        self.grok2api_admin_username_var = tk.StringVar(
            value=str(config.get("grok2api_admin_username", ""))
        )
        # Grok2API 管理员密码仅写入本机 config.json，并以掩码形式显示。
        self.grok2api_admin_password_var = tk.StringVar(
            value=str(config.get("grok2api_admin_password", ""))
        )
        c_label(2, 0, "CPA 本地备用:")
        c_field(tk_entry(self.cpa_frame, textvariable=self.cpa_auth_dir_var, width=52), 2, 1, columnspan=3)
        c_label(3, 0, "CPA 服务器地址:")
        c_field(tk_entry(self.cpa_frame, textvariable=self.cpa_remote_url_var, width=34), 3, 1)
        c_label(3, 2, "CPA 管理密钥:")
        c_field(
            tk_entry(
                self.cpa_frame,
                textvariable=self.cpa_management_key_var,
                width=28,
                show="*",
            ),
            3,
            3,
        )
        c_label(4, 0, "Grok2API 本地备用:")
        c_field(tk_entry(self.cpa_frame, textvariable=self.grok2api_auth_dir_var, width=52), 4, 1, columnspan=3)
        c_label(5, 0, "Grok2API 服务器地址:")
        c_field(
            tk_entry(
                self.cpa_frame,
                textvariable=self.grok2api_remote_url_var,
                width=52,
            ),
            5,
            1,
            columnspan=3,
        )
        c_label(6, 0, "Grok2API 管理员:")
        c_field(
            tk_entry(
                self.cpa_frame,
                textvariable=self.grok2api_admin_username_var,
                width=34,
            ),
            6,
            1,
        )
        c_label(6, 2, "Grok2API 管理密码:")
        c_field(
            tk_entry(
                self.cpa_frame,
                textvariable=self.grok2api_admin_password_var,
                width=28,
                show="*",
            ),
            6,
            3,
        )

        self.email_provider_var.trace_add("write", lambda *_: self._refresh_provider_fields())
        self.proxy_mode_var.trace_add("write", lambda *_: self._refresh_proxy_fields())
        self.resin_enable_tunnel_var.trace_add(
            "write",
            lambda *_: self._refresh_proxy_fields(),
        )
        self.cpa_auto_add_var.trace_add("write", lambda *_: self._refresh_cpa_fields())
        self._refresh_provider_fields()
        self._refresh_proxy_fields()
        self._refresh_cpa_fields()
        self._bind_config_mousewheel_tree(config_scroll_host)

        btn_frame = tk.Frame(main_frame, bg=UI_BG)
        btn_frame.grid(row=1, column=0, sticky=tk.EW, pady=(0, 6))
        self.start_btn = tk_button(btn_frame, text="开始注册", command=self.start_registration)
        self.start_btn.pack(side=tk.LEFT, padx=5)
        # sso_recovery_btn 只处理本地恢复队列，按钮数字随有效记录数量动态更新。
        self.sso_recovery_btn = tk_button(
            btn_frame,
            text="重新获取未获取到的SSO 账号（0）",
            command=self.start_sso_recovery,
        )
        self.sso_recovery_btn.pack(side=tk.LEFT, padx=5)
        self.stop_btn = tk_button(btn_frame, text="停止", command=self.stop_registration, state=tk.DISABLED)
        self.stop_btn.pack(side=tk.LEFT, padx=5)
        self.close_browser_on_stop_var = tk.BooleanVar(
            value=bool(config.get("close_browser_on_stop", False))
        )
        self.close_browser_on_stop_check = tk_checkbutton(
            btn_frame,
            text="停止时关闭浏览器",
            variable=self.close_browser_on_stop_var,
        )
        self.close_browser_on_stop_check.pack(side=tk.LEFT, padx=(2, 8))
        self.check_btn = tk_button(btn_frame, text="连通性检查", command=self.run_connectivity_check)
        self.check_btn.pack(side=tk.LEFT, padx=5)
        self.clear_btn = tk_button(btn_frame, text="清空日志", command=self.clear_log)
        self.clear_btn.pack(side=tk.LEFT, padx=5)
        self._refresh_sso_recovery_button()

        status_frame = tk.Frame(main_frame, bg=UI_BG)
        status_frame.grid(row=2, column=0, sticky=tk.EW, pady=(0, 6))
        self.status_var = tk.StringVar(value="就绪")
        tk_label(status_frame, text="状态: ").pack(side=tk.LEFT)
        self.status_label = tk.Label(status_frame, textvariable=self.status_var, bg=UI_BG, fg="green")
        self.status_label.pack(side=tk.LEFT)
        self.progress_var = tk.DoubleVar(value=0.0)
        self.progress_bar = ttk.Progressbar(
            status_frame, variable=self.progress_var, maximum=100, length=180, mode="determinate"
        )
        self.progress_bar.pack(side=tk.LEFT, padx=(16, 8))
        self.eta_var = tk.StringVar(value="进度 0/0 | ETA --")
        tk.Label(status_frame, textvariable=self.eta_var, bg=UI_BG, fg=UI_MUTED_FG).pack(side=tk.LEFT)
        self.stats_var = tk.StringVar(value="成功: 0 | 失败: 0")
        tk.Label(status_frame, textvariable=self.stats_var, bg=UI_BG, fg=UI_FG).pack(side=tk.RIGHT)
        log_frame = tk.LabelFrame(
            main_frame,
            text="日志",
            bg=UI_PANEL_BG,
            fg=UI_FG,
            padx=5,
            pady=5,
            relief=tk.GROOVE,
            borderwidth=1,
        )
        log_frame.grid(row=3, column=0, sticky=tk.NSEW)
        log_frame.grid_columnconfigure(0, weight=1)
        log_frame.grid_rowconfigure(0, weight=1)
        self.log_text = scrolledtext.ScrolledText(
            log_frame,
            height=18,
            width=60,
            bg="#ffffff",
            fg=UI_FG,
            insertbackground=UI_FG,
            selectbackground="#bfdbfe",
            selectforeground=UI_FG,
            relief=tk.SOLID,
            borderwidth=1,
            highlightthickness=1,
            highlightbackground="#cbd5e1",
        )
        self.log_text.grid(row=0, column=0, sticky=tk.NSEW)
        self.log("[*] GUI 已就绪，配置已加载")
        self.log(f"[*] 当前邮箱服务商: {self.email_provider_var.get()} | 注册数量: {self.count_var.get()}")
        self.log(f"[*] 当前代理类型: {self.proxy_mode_var.get()}")

    def _refresh_provider_fields(self):
        """按当前邮箱服务商只显示相关配置项。"""
        provider = (self.email_provider_var.get() or "cloudflare").strip().lower()
        titles = {
            "outlook_email": "OutlookEmail 完整 API 配置",
            "icloud": "iCloud Hide My Email 配置",
            "duckmail": "DuckMail / Mail.tm 配置",
            "cloudflare": "Cloudflare 配置",
            "yyds": "YYDS 配置",
            "mailnest": "MailNest 配置",
            "cloudmail": "CloudMail 配置",
        }
        self.provider_frame.configure(text=titles.get(provider, "邮箱服务商配置"))
        for widgets in self._provider_widget_groups.values():
            for widget in widgets:
                widget.grid_remove()
        for widget in self._provider_widget_groups.get(provider, self._cloudflare_widgets):
            # grid_remove 后无参 grid() 会恢复原行列
            widget.grid()

    def _apply_icloud_ui_config(self):
        """把 GUI 中的 iCloud HME 和 SSH 隧道字段写回内存配置。"""
        config["icloud_api_base"] = (
            self.icloud_api_base_var.get().strip() or "http://127.0.0.1:18090"
        )
        config["icloud_enable_tunnel"] = bool(
            self.icloud_enable_tunnel_var.get()
        )
        config["icloud_ssh_key"] = (
            self.icloud_ssh_key_var.get().strip()
            or "~/.ssh/MaXiangLinTxCloudMiYao.pem"
        )
        config["icloud_ssh_user"] = (
            self.icloud_ssh_user_var.get().strip() or "ubuntu"
        )
        config["icloud_ssh_host"] = self.icloud_ssh_host_var.get().strip()
        config["icloud_local_port"] = int(
            self.icloud_local_port_var.get().strip() or "18090"
        )
        config["icloud_remote_port"] = int(
            self.icloud_remote_port_var.get().strip() or "8090"
        )

    def _apply_outlook_email_ui_config(self):
        """把 GUI 中的完整 API 登录、项目和可选分组范围写回配置。"""
        raw_group_ids = self.outlook_email_group_ids_var.get().strip()
        group_ids = []
        for item in raw_group_ids.split(",") if raw_group_ids else []:
            text = item.strip()
            if not text:
                continue
            group_id = int(text)
            if group_id <= 0:
                raise ValueError("OutlookEmail 分组 ID 必须为正整数")
            if group_id not in group_ids:
                group_ids.append(group_id)
        config["outlook_email_base_url"] = (
            self.outlook_email_base_url_var.get().strip().rstrip("/")
        )
        config["outlook_email_login_password"] = (
            self.outlook_email_login_password_var.get()
        )
        config["outlook_email_project_key"] = (
            self.outlook_email_project_key_var.get().strip().lower()
            or "grok-register"
        )
        config["outlook_email_group_ids"] = group_ids
        config["outlook_email_use_alias_email"] = bool(
            self.outlook_email_use_alias_email_var.get()
        )

    def _refresh_proxy_fields(self):
        """按代理类型和通道开关分级显示 Resin 认证及 SSH 连接参数。"""
        resin_enabled = "resin" in self.proxy_mode_var.get().strip().lower()
        if resin_enabled:
            self.resin_frame.grid()
            self.resin_tunnel_check.grid()
            if self.resin_enable_tunnel_var.get():
                self.resin_ssh_frame.grid()
            else:
                self.resin_ssh_frame.grid_remove()
        else:
            self.resin_frame.grid_remove()
            self.resin_ssh_frame.grid_remove()
            self.resin_tunnel_check.grid_remove()

    def _apply_proxy_ui_config(self):
        """把 GUI 代理、Resin 身份和独立 SSH 隧道字段写回配置。"""
        mode_text = self.proxy_mode_var.get().strip().lower()
        config["proxy_mode"] = (
            PROXY_MODE_RESIN if "resin" in mode_text else PROXY_MODE_NORMAL
        )
        config["proxy"] = self.proxy_var.get().strip()
        config["resin_token"] = self.resin_token_var.get()
        config["resin_platform"] = (
            self.resin_platform_var.get().strip() or RESIN_DEFAULT_PLATFORM
        )
        config["resin_enable_tunnel"] = bool(
            self.resin_enable_tunnel_var.get()
        )
        config["resin_ssh_key"] = (
            self.resin_ssh_key_var.get().strip()
            or "~/.ssh/MaXiangLinTxCloudMiYao.pem"
        )
        config["resin_ssh_user"] = (
            self.resin_ssh_user_var.get().strip() or "ubuntu"
        )
        config["resin_ssh_host"] = self.resin_ssh_host_var.get().strip()
        config["resin_local_port"] = (
            self.resin_local_port_var.get().strip() or "12260"
        )
        config["resin_remote_port"] = (
            self.resin_remote_port_var.get().strip() or "2260"
        )
        normalized_proxy = normalize_resin_tunnel_proxy(config)
        if normalized_proxy != self.proxy_var.get().strip():
            # 首次从本机 2260 迁移到 SSH 本地端口时同步更新可见输入框。
            self.proxy_var.set(normalized_proxy)

    def _apply_auth_output_ui_config(self):
        """把 GUI 中的 SSO 换取方式、输出目标和远程凭据写回配置。"""
        config["cpa_auto_add"] = bool(self.cpa_auto_add_var.get())
        config["cpa_enabled"] = bool(self.cpa_enabled_var.get())
        config["grok2api_enabled"] = bool(self.grok2api_enabled_var.get())
        mode_text = str(self.cpa_token_mode_var.get()).strip()
        if "协议" in mode_text:
            config["cpa_token_mode"] = "device_protocol"
        elif "浏览器" in mode_text:
            config["cpa_token_mode"] = "device_browser"
        elif "auth" in mode_text.lower() or "code" in mode_text.lower():
            config["cpa_token_mode"] = "auth_code"
        else:
            config["cpa_token_mode"] = "device_protocol"
        config["cpa_auth_dir"] = self.cpa_auth_dir_var.get().strip()
        config["cpa_remote_url"] = self.cpa_remote_url_var.get().strip()
        config["cpa_management_key"] = self.cpa_management_key_var.get().strip()
        config["grok2api_auth_dir"] = self.grok2api_auth_dir_var.get().strip()
        config["grok2api_remote_url"] = self.grok2api_remote_url_var.get().strip()
        config["grok2api_admin_username"] = (
            self.grok2api_admin_username_var.get().strip()
        )
        config["grok2api_admin_password"] = self.grok2api_admin_password_var.get()

    def _refresh_cpa_fields(self):
        """未开启 SSO→auth 时隐藏 CPA 与 Grok2API 的交付配置。"""
        enabled = bool(self.cpa_auto_add_var.get())
        for widget in getattr(self, "_cpa_detail_widgets", []):
            if enabled:
                widget.grid()
            else:
                widget.grid_remove()

    def log(self, message):
        """把脱敏后的消息同时写入控制台、会话日志和 GUI 日志框。"""
        message = redact_sensitive_text(message)
        if not should_emit_log(message):
            return
        if self._queue_ui_call(self.log, message):
            return
        timestamp = datetime.datetime.now().strftime("%H:%M:%S")
        line = f"[{timestamp}] {message}"
        append_session_log(line)
        print(line, flush=True)
        self.log_text.insert(tk.END, f"{line}\n")
        self.log_text.see(tk.END)

    def clear_log(self):
        self.log_text.delete(1.0, tk.END)

    def update_stats(self):
        if self._queue_ui_call(self.update_stats):
            return
        fail_detail = format_fail_stats(getattr(self, "fail_stats", {}) or {})
        if self.fail_count:
            self.stats_var.set(
                f"成功: {self.success_count} | 失败: {self.fail_count}（{fail_detail}）"
            )
        else:
            self.stats_var.set(f"成功: {self.success_count} | 失败: 0")
        self._update_progress()

    def _update_progress(self):
        total = max(int(getattr(self, "batch_count", 0) or 0), 1)
        done = int(self.success_count) + int(self.fail_count)
        pct = min(100.0, 100.0 * done / total)
        if hasattr(self, "progress_var"):
            self.progress_var.set(pct)
        # ETA
        started = getattr(self, "_batch_started_at", None)
        eta_text = "ETA --"
        if started and done > 0:
            elapsed = max(time.time() - started, 0.1)
            rate = done / elapsed
            remain = max(total - done, 0)
            if rate > 0:
                sec = int(remain / rate)
                if sec < 60:
                    eta_text = f"ETA {sec}s"
                else:
                    eta_text = f"ETA {sec // 60}m{sec % 60:02d}s"
        if hasattr(self, "eta_var"):
            self.eta_var.set(f"进度 {done}/{total} | {eta_text}")

    def run_connectivity_check(self):
        """后台建立可选 Resin 隧道并检查代理、邮箱 API 和 auth 输出目标。"""
        # 先把当前 GUI 关键字段写回内存配置（不强制保存文件）
        try:
            config["email_provider"] = self.email_provider_var.get().strip() or "cloudflare"
            self._apply_proxy_ui_config()
            config["duckmail_api_key"] = self.api_key_var.get().strip()
            config["duckmail_api_base"] = self.duckmail_api_base_var.get().strip()
            config["cloudflare_api_base"] = self.cloudflare_api_base_var.get().strip()
            config["cloudflare_api_key"] = self.cloudflare_api_key_var.get().strip()
            config["cloudflare_auth_mode"] = self.cloudflare_auth_mode_var.get().strip() or "none"
            config["defaultDomains"] = self.default_domains_var.get().strip()
            config["cloudflare_custom_auth"] = self.cloudflare_custom_auth_var.get().strip()
            config["yyds_api_key"] = self.yyds_api_key_var.get().strip()
            config["yyds_jwt"] = self.yyds_jwt_var.get().strip()
            config["mailnest_api_key"] = self.mailnest_api_key_var.get().strip()
            config["cloudmail_url"] = self.cloudmail_url_var.get().strip()
            config["cloudmail_admin_email"] = self.cloudmail_admin_email_var.get().strip()
            config["cloudmail_password"] = self.cloudmail_password_var.get()
            self._apply_icloud_ui_config()
            self._apply_outlook_email_ui_config()
            self._apply_auth_output_ui_config()
            validate_proxy_config()
            tunnel_config = dict(config)
            check_config = connectivity_config_for_proxy()
        except Exception as exc:
            self.log(f"[!] 当前配置无法用于连通性检查: {exc}")
            return
        self.log("[*] 开始连通性检查...")
        self.check_btn.config(state=tk.DISABLED)

        def _job():
            """在后台线程执行连通性检查，避免阻塞 Tk 主事件循环。"""
            try:
                if is_resin_proxy_mode(tunnel_config):
                    _resin_tunnel.ensure(
                        tunnel_config,
                        log_callback=self.log,
                    )
                results = _conn.run_connectivity_checks(
                    check_config,
                    http_get,
                    http_post,
                )
                text = _conn.format_check_results(results)
                all_ok = all(ok for _, ok, _ in results)
                self.ui_queue.put((self._on_check_done, (text, all_ok)))
            except Exception as exc:
                self.ui_queue.put((self._on_check_done, (f"检查异常: {exc}", False)))

        threading.Thread(target=_job, daemon=True).start()

    def _on_check_done(self, text, all_ok):
        self.check_btn.config(state=tk.NORMAL)
        for line in str(text).splitlines():
            self.log(f"[检查] {line}")
        self.status_var.set("检查通过" if all_ok else "检查有失败项")
        self.status_label.config(foreground="green" if all_ok else "orange")

    def _record_failure(self, exc):
        kind = classify_failure(exc)
        lock = getattr(self, "_stats_lock", None)
        if lock:
            with lock:
                self.fail_count += 1
                if not hasattr(self, "fail_stats") or self.fail_stats is None:
                    self.fail_stats = empty_fail_stats()
                self.fail_stats[kind] = self.fail_stats.get(kind, 0) + 1
        else:
            self.fail_count += 1
            if not hasattr(self, "fail_stats") or self.fail_stats is None:
                self.fail_stats = empty_fail_stats()
            self.fail_stats[kind] = self.fail_stats.get(kind, 0) + 1
        return kind

    def _record_success(self):
        lock = getattr(self, "_stats_lock", None)
        if lock:
            with lock:
                self.success_count += 1
        else:
            self.success_count += 1

    def _refresh_sso_recovery_button(self):
        """刷新独立恢复按钮的队列数量，并在无任务时按数量决定是否可点击。"""
        if self._queue_ui_call(self._refresh_sso_recovery_button):
            return
        pending_count = get_sso_recovery_count()
        self.sso_recovery_btn.config(
            text=f"重新获取未获取到的SSO 账号（{pending_count}）"
        )
        if not self.is_running:
            self.sso_recovery_btn.config(
                state=tk.NORMAL if pending_count > 0 else tk.DISABLED
            )

    def _set_running_ui(self, running):
        """统一切换注册与 SSO 恢复任务的互斥按钮和状态栏显示。"""
        if self._queue_ui_call(self._set_running_ui, running):
            return
        self.is_running = running
        self.start_btn.config(state=tk.DISABLED if running else tk.NORMAL)
        self.sso_recovery_btn.config(state=tk.DISABLED)
        self.stop_btn.config(state=tk.NORMAL if running else tk.DISABLED)
        self.status_var.set("运行中..." if running else "就绪")
        self.status_label.config(foreground="blue" if running else "green")
        if not running:
            self.active_task_kind = ""
            self._refresh_sso_recovery_button()

    def should_stop(self):
        return self.stop_requested or not self.is_running

    def start_sso_recovery(self):
        """校验代理与 SSO 输出配置，并启动不依赖邮箱 API 的独立恢复任务。"""
        if self.is_running:
            self.log("[!] 当前已有任务在运行")
            return
        pending_count = get_sso_recovery_count()
        if pending_count <= 0:
            self.log("[*] 当前没有未获取到 SSO 的待处理账号")
            self._refresh_sso_recovery_button()
            return

        config["debug_mode"] = bool(self.debug_mode_var.get())
        config["close_browser_on_stop"] = bool(self.close_browser_on_stop_var.get())
        config["log_level"] = (self.log_level_var.get().strip() or "info").lower()
        try:
            self._apply_proxy_ui_config()
            validate_proxy_config()
        except ValueError as proxy_exc:
            self.log(f"[!] 代理配置无效: {proxy_exc}")
            return
        self._apply_auth_output_ui_config()
        if (
            config.get("cpa_auto_add")
            and any(get_auth_output_selection())
            and not has_selected_auth_output_target()
        ):
            self.log("[!] 已开启 SSO→auth，但勾选的输出目标没有配置远程地址或本地备用目录")
            return
        save_config()

        # 恢复任务拥有独立代理批次，避免沿用上一次注册任务的 Resin Account。
        recovery_batch_id = new_resin_batch_id()
        load_proxy_pool()
        self.stop_requested = False
        self.success_count = 0
        self.fail_count = 0
        self.fail_stats = empty_fail_stats()
        self.results = []
        self.batch_count = pending_count
        self._batch_started_at = time.time()
        self.progress_var.set(0)
        self.eta_var.set(f"进度 0/{pending_count} | ETA --")
        self._stats_lock = threading.Lock()
        self._accounts_lock = threading.Lock()
        self.active_task_kind = "sso_recovery"
        self.update_stats()
        self._set_running_ui(True)
        self.status_var.set("正在重新获取 SSO...")
        self.status_label.config(foreground="blue")
        self.log(
            f"[*] 开始独立 SSO 恢复任务，待处理账号: {pending_count}；"
            "本任务不检查或调用邮箱 API"
        )
        threading.Thread(
            target=self._run_sso_recovery_entry,
            args=(recovery_batch_id,),
            daemon=True,
        ).start()

    def _run_sso_recovery_entry(self, recovery_batch_id):
        """在后台准备代理并处理恢复队列，结束后只汇总本次 SSO 恢复结果。"""
        prepare_sso_recovery_run()
        try:
            try:
                _cleanup_stale_profiles(log_callback=self.log)
            except Exception:
                pass
            if is_resin_proxy_mode(config):
                _resin_tunnel.ensure(config, log_callback=self.log)
            bound_proxy, resin_account = bind_proxy_for_account(
                recovery_batch_id,
                0,
                0,
            )
            if resin_account:
                self.log(
                    "[*] SSO 恢复代理已绑定: "
                    f"Platform={config.get('resin_platform', RESIN_DEFAULT_PLATFORM)} "
                    f"Account={resin_account} 入口={redact_proxy(bound_proxy)}"
                )
            else:
                self.log(
                    f"[*] SSO 恢复代理已绑定: {redact_proxy(bound_proxy) or '直连'}"
                )
            result = recover_pending_sso_accounts(
                log_callback=self.log,
                cancel_callback=self.should_stop,
            )
            self.success_count = int(result.get("success", 0) or 0)
            self.fail_count = int(result.get("failed", 0) or 0)
            self.update_stats()
            self.log(
                f"[*] SSO 恢复任务结束。成功 {self.success_count} | "
                f"失败 {self.fail_count}"
            )
        except RegistrationCancelled:
            self.log("[!] SSO 恢复任务已由用户停止")
        except Exception as exc:
            self.log(f"[!] SSO 恢复任务异常: {exc}")
        finally:
            try:
                maybe_stop_browser(
                    user_stopped=bool(self.stop_requested),
                    log_callback=self.log,
                )
            except BaseException:
                pass
            self._set_running_ui(False)

    def start_registration(self):
        """校验 GUI 配置并启动本轮注册任务。"""
        if self.is_running:
            self.log("[!] 当前已有任务在运行")
            return

        config["email_provider"] = self.email_provider_var.get().strip() or "cloudflare"
        config["debug_mode"] = bool(self.debug_mode_var.get())
        config["close_browser_on_stop"] = bool(self.close_browser_on_stop_var.get())
        config["log_level"] = (self.log_level_var.get().strip() or "info").lower()
        self._apply_proxy_ui_config()
        config["duckmail_api_key"] = self.api_key_var.get().strip()
        config["duckmail_api_base"] = self.duckmail_api_base_var.get().strip() or DUCKMAIL_API_BASE_DEFAULT
        config["cloudflare_api_base"] = self.cloudflare_api_base_var.get().strip()
        config["cloudflare_api_key"] = self.cloudflare_api_key_var.get().strip()
        config["cloudflare_auth_mode"] = self.cloudflare_auth_mode_var.get().strip() or "none"
        config["defaultDomains"] = self.default_domains_var.get().strip()
        config["cloudflare_custom_auth"] = self.cloudflare_custom_auth_var.get().strip()
        config["yyds_api_key"] = self.yyds_api_key_var.get().strip()
        config["yyds_jwt"] = self.yyds_jwt_var.get().strip()
        config["mailnest_api_key"] = self.mailnest_api_key_var.get().strip()
        config["mailnest_project_code"] = (
            self.mailnest_project_code_var.get().strip() or MAILNEST_DEFAULT_PROJECT_CODE
        )
        config["yyds_default_domain"] = self.yyds_default_domain_var.get().strip()
        config["cloudmail_url"] = self.cloudmail_url_var.get().strip()
        config["cloudmail_admin_email"] = self.cloudmail_admin_email_var.get().strip()
        config["cloudmail_password"] = self.cloudmail_password_var.get()
        try:
            self._apply_icloud_ui_config()
            self._apply_outlook_email_ui_config()
        except ValueError:
            self.log("[!] iCloud 端口或 OutlookEmail 分组 ID 配置无效")
            return
        self._apply_auth_output_ui_config()
        raw_paths = [x.strip() for x in self.cloudflare_paths_var.get().split(",") if x.strip()]
        if len(raw_paths) >= 4:
            config["cloudflare_path_domains"] = raw_paths[0] if raw_paths[0].startswith("/") else ("/" + raw_paths[0])
            config["cloudflare_path_accounts"] = raw_paths[1] if raw_paths[1].startswith("/") else ("/" + raw_paths[1])
            config["cloudflare_path_token"] = raw_paths[2] if raw_paths[2].startswith("/") else ("/" + raw_paths[2])
            config["cloudflare_path_messages"] = raw_paths[3] if raw_paths[3].startswith("/") else ("/" + raw_paths[3])
        config["account_interval"] = self.account_interval_var.get().strip() or "0"
        try:
            validate_proxy_config()
        except ValueError as proxy_exc:
            self.log(f"[!] 代理配置无效: {proxy_exc}")
            return
        save_config()
        if config["email_provider"] == "cloudflare" and not config["cloudflare_api_base"]:
            self.log("[!] Cloudflare 模式需要先填写 Cloudflare API Base")
            return
        if config["email_provider"] == "mailnest" and not config["mailnest_api_key"]:
            self.log("[!] MailNest 模式需要先填写 MailNest API Key")
            return
        if config["email_provider"] == "cloudmail":
            missing = []
            if not get_cloudmail_url():
                missing.append("CloudMail URL")
            if not get_cloudmail_admin_email():
                missing.append("CloudMail 管理员邮箱")
            if not get_cloudmail_password():
                missing.append("CloudMail 管理员密码")
            if not config["defaultDomains"]:
                missing.append("默认收信域名")
            if missing:
                self.log(f"[!] CloudMail 模式缺少配置: {', '.join(missing)}")
                return
        if config["email_provider"] == "icloud":
            if not str(config.get("icloud_api_base", "") or "").strip():
                self.log("[!] iCloud 模式需要配置本地 API Base")
                return
            if config.get("icloud_enable_tunnel") and not str(
                config.get("icloud_ssh_host", "") or ""
            ).strip():
                self.log("[!] iCloud 自动隧道模式需要配置 SSH 主机")
                return
        if config["email_provider"] == "outlook_email":
            if not str(config.get("outlook_email_base_url", "") or "").strip():
                self.log("[!] OutlookEmail 模式需要填写服务地址")
                return
            if not str(
                config.get("outlook_email_login_password", "") or ""
            ):
                self.log("[!] OutlookEmail 模式需要填写 Web 登录密码")
                return
        if (
            config.get("cpa_auto_add")
            and any(get_auth_output_selection())
            and not has_selected_auth_output_target()
        ):
            self.log("[!] 已开启 SSO→auth，但勾选的输出目标没有配置远程地址或本地备用目录")
            return
        try:
            count = int(self.count_var.get())
        except Exception:
            self.log("[!] 注册数量无效")
            return
        try:
            workers = int(self.workers_var.get())
        except Exception:
            workers = 1
        if config.get("debug_mode"):
            if count != 1 or workers != 1:
                self.log("[*] 调试模式：强制 数量=1、并发=1，结束后不关闭浏览器")
            count = 1
            workers = 1
            self.count_var.set("1")
            self.workers_var.set("1")
        workers = max(1, min(workers, 24, count))
        config["register_count"] = count
        config["register_workers"] = workers
        save_config()
        # _proxy_batch_id 保证本轮每个账号的 Resin Account 唯一且可重复计算。
        self._proxy_batch_id = new_resin_batch_id()
        load_proxy_pool()
        self.stop_requested = False
        self.success_count = 0
        self.fail_count = 0
        self.fail_stats = empty_fail_stats()
        self.results = []
        self.batch_count = count
        self._batch_started_at = None
        self.progress_var.set(0)
        self.eta_var.set(f"进度 0/{count} | ETA --")
        self.update_stats()
        self.active_task_kind = "registration"
        self._set_running_ui(True)
        self.status_var.set("正在检查...")
        self.status_label.config(foreground="blue")
        self._stats_lock = threading.Lock()
        self._accounts_lock = threading.Lock()
        self.log("[*] 正在执行启动前连通性检查...")
        threading.Thread(
            target=self._run_startup_connectivity_check,
            args=(count, workers, dict(config), self._proxy_batch_id),
            daemon=True,
        ).start()

    def _run_startup_connectivity_check(
        self,
        count,
        workers,
        check_config,
        batch_id,
    ):
        """在后台确保 Resin 隧道并执行三次 xAI 重试，再把结果交回主线程。"""
        checks = []
        error_text = ""
        startup_resin_generation = 0
        startup_attempts = 0
        try:
            if is_resin_proxy_mode(check_config):
                _resin_tunnel.ensure(
                    check_config,
                    log_callback=self.log,
                )
            (
                checks,
                startup_resin_generation,
                startup_attempts,
            ) = run_startup_checks_with_xai_retries(
                check_config,
                batch_id,
                log_callback=self.log,
                cancel_callback=self.should_stop,
            )
        except Exception as exc:
            error_text = str(exc)
        self.ui_queue.put(
            (
                self._on_startup_connectivity_done,
                (
                    count,
                    workers,
                    checks,
                    error_text,
                    startup_resin_generation,
                    startup_attempts,
                ),
            )
        )

    def _on_startup_connectivity_done(
        self,
        count,
        workers,
        checks,
        error_text,
        startup_resin_generation,
        startup_attempts,
    ):
        """展示启动检查结果，失败三次时终止，否则启动并复用已验证出口。"""
        for name, ok, detail in checks:
            # 多次重试时，后台已逐次输出 xAI 结果，此处避免重复打印最后一次。
            if (
                startup_attempts > 1
                and name == _conn.XAI_SIGNUP_CHECK_NAME
            ):
                continue
            self.log(f"[检查] [{'OK' if ok else 'FAIL'}] {name}: {detail}")
        if error_text:
            self.log(f"[!] 连通性检查异常: {error_text}")

        # 用户可在后台检查期间点击停止；检查返回后不得再启动浏览器。
        if self.stop_requested or not self.is_running:
            self.log("[*] 启动已取消，未进入注册流程")
            self._set_running_ui(False)
            return
        if error_text:
            self.log("[!] 启动前准备失败，已停止建号")
            self._set_running_ui(False)
            return
        if _conn.has_blocking_xai_failure(checks):
            last_detail = next(
                (
                    detail
                    for name, ok, detail in checks
                    if name == _conn.XAI_SIGNUP_CHECK_NAME and not ok
                ),
                "未知错误",
            )
            self.log(
                f"[!] xAI 注册页启动检查连续 "
                f"{startup_attempts or XAI_STARTUP_CHECK_ATTEMPTS} 次失败，"
                f"已停止建号；最后原因: {last_detail}"
            )
            self._set_running_ui(False)
            return
        if checks and not all(ok for _, ok, _ in checks):
            self.log("[!] 连通性检查存在失败项，仍继续注册（可先点「连通性检查」排查）")

        self._batch_started_at = time.time()
        self.status_var.set("运行中...")
        self.status_label.config(foreground="blue")
        _interval_raw = str(config.get("account_interval", "0") or "0").strip()
        _interval_info = f" | 账号间隔: {_interval_raw}s" if _interval_raw and _interval_raw != "0" else ""
        self.log(
            f"[*] 配置已保存，开始执行。目标数量: {count} | 并发: {workers}{_interval_info}"
            + (" | 调试模式" if config.get("debug_mode") else "")
        )
        if is_resin_proxy_mode():
            self.log(
                "[*] Resin 粘性代理: "
                f"Platform={config.get('resin_platform', RESIN_DEFAULT_PLATFORM)}，"
                "每个账号使用独立 Account"
            )
        if int(self.workers_var.get() or 1) > count and not config.get("debug_mode"):
            self.log(f"[*] 并发已自动调整为 {workers}（不超过注册数量）")
        _mode_map = {"device_protocol": "协议 Device Flow", "device_browser": "浏览器 Device Flow", "auth_code": "Authorization Code"}
        _mode_label = _mode_map.get(str(config.get("cpa_token_mode", "device_protocol")), "协议 Device Flow")
        _output_names = [
            name
            for name, selected in zip(
                ("CPA", "Grok2API"),
                get_auth_output_selection(),
            )
            if selected
        ]
        _output_detail = f"，输出={'/'.join(_output_names) or '未勾选'}"
        self.log(
            f"[*] SSO→auth: {'开' if config.get('cpa_auto_add') else '关（仅保存 SSO）'}"
            + (
                f"（{_mode_label}{_output_detail}）"
                if config.get("cpa_auto_add")
                else ""
            )
        )
        threading.Thread(
            target=self._run_registration_entry,
            args=(count, workers, startup_resin_generation),
            daemon=True,
        ).start()

    def stop_registration(self):
        """请求停止当前注册或 SSO 恢复任务，并按用户设置决定是否保留浏览器。"""
        self.stop_requested = True
        # 即时写入，worker finally 能读到最新勾选状态
        config["close_browser_on_stop"] = bool(self.close_browser_on_stop_var.get())
        keep = not config.get("close_browser_on_stop", False)
        task_name = "SSO 恢复" if self.active_task_kind == "sso_recovery" else "注册"
        self.log(
            f"[!] 用户停止{task_name}"
            + ("（将保留浏览器）" if keep else "（将关闭浏览器）")
        )

    def _run_registration_entry(
        self,
        count,
        workers,
        startup_resin_generation=0,
    ):
        """协调 GUI worker，并让首个 worker 复用启动检查通过的 Resin 代次。"""
        # 并发数不超过任务数，避免空 worker 白开浏览器
        workers = max(1, min(int(workers or 1), 24, int(count or 1)))
        # 启动前清理上次崩溃 / 强杀残留的临时 profile 目录
        try:
            _cleanup_stale_profiles(log_callback=self.log)
        except Exception:
            pass
        try:
            if workers <= 1:
                self.run_registration(
                    count,
                    worker_id=0,
                    workers=1,
                    startup_resin_generation=startup_resin_generation,
                )
            else:
                base, rem = divmod(count, workers)
                chunks = [base + (1 if i < rem else 0) for i in range(workers)]
                # 去掉 0 任务分片，重新编号
                chunks = [n for n in chunks if n > 0]
                self.log(f"[*] 实际并发 worker={len(chunks)}，分片={chunks}")
                threads = []
                for wid, n in enumerate(chunks):
                    t = threading.Thread(
                        target=self.run_registration,
                        kwargs={
                            "count": n,
                            "worker_id": wid,
                            "workers": len(chunks),
                            "startup_resin_generation": (
                                startup_resin_generation if wid == 0 else 0
                            ),
                        },
                        daemon=True,
                    )
                    t.start()
                    threads.append(t)
                    # 错开启动，降低同时拉起 Chrome 端口/用户目录冲突
                    time.sleep(2.0)
                for t in threads:
                    t.join()
        finally:
            # 协调线程自身无浏览器；各 worker 线程 finally 已各自 stop
            self._set_running_ui(False)
            self.log(
                f"[*] 任务结束。成功 {self.success_count} | 失败 {self.fail_count}"
                + (f" | {format_fail_stats(self.fail_stats)}" if self.fail_count else "")
            )

    def run_registration(
        self,
        count,
        worker_id=0,
        workers=1,
        startup_resin_generation=0,
    ):
        """执行 GUI 注册，并让首个账号沿用预检成功的 Resin 粘性出口。"""
        prefix = f"[W{worker_id + 1}] " if workers > 1 else ""
        batch_id = str(
            getattr(self, "_proxy_batch_id", "") or new_resin_batch_id()
        )

        def wlog(message):
            text = str(message)
            if prefix and not text.startswith(prefix):
                self.log(prefix + text)
            else:
                self.log(text)

        try:
            i = 0
            bound_proxy, resin_account = bind_proxy_for_account(
                batch_id,
                worker_id,
                i,
                resin_generation=(
                    startup_resin_generation
                    if worker_id == 0 and i == 0
                    else None
                ),
            )
            logged_proxy_index = i
            if resin_account:
                wlog(
                    "[*] Resin 账号代理已绑定: "
                    f"Platform={config.get('resin_platform', RESIN_DEFAULT_PLATFORM)} "
                    f"Account={resin_account} 入口={redact_proxy(bound_proxy)}"
                )
            else:
                wlog(f"[*] 账号代理已绑定: {redact_proxy(bound_proxy) or '直连'}")
            try:
                start_browser(log_callback=wlog)
            except Exception as boot_exc:
                streak = get_start_fail_streak()
                wlog(f"[-] 浏览器启动失败 (连续失败 {streak}): {boot_exc}")
                if workers > 1 and streak >= 3:
                    wlog("[!] 连续启动失败较多，建议降低并发后重试")
                for _ in range(max(int(count or 0), 0)):
                    self._record_failure(boot_exc)
                self.update_stats()
                return
            wlog("[*] 浏览器已启动")
            retry_count_for_slot = 0
            max_slot_retry = 3
            while i < count:
                if self.should_stop():
                    break
                bound_proxy, resin_account = bind_proxy_for_account(
                    batch_id,
                    worker_id,
                    i,
                )
                if logged_proxy_index != i:
                    logged_proxy_index = i
                    if resin_account:
                        wlog(
                            "[*] 下一个账号使用新的 Resin 租约: "
                            f"Platform={config.get('resin_platform', RESIN_DEFAULT_PLATFORM)} "
                            f"Account={resin_account} 入口={redact_proxy(bound_proxy)}"
                        )
                    else:
                        wlog(
                            f"[*] 下一个账号代理: {redact_proxy(bound_proxy) or '直连'}"
                        )
                wlog(f"--- 开始第 {i + 1}/{count} 个账号 ---")
                # 邮箱领取后默认释放；只有确认资料已提交才改为成功，永久拒绝才改为失败。
                provider_claim_outcome = "release"
                provider_claim_detail = "注册资料尚未确认提交，释放邮箱供下次使用"
                try:
                    email = ""
                    dev_token = ""
                    code = ""
                    mail_ok = False
                    max_mail_retry = 3
                    for mail_try in range(1, max_mail_retry + 1):
                        wlog(f"[*] 1. 打开注册页 (尝试 {mail_try}/{max_mail_retry})")
                        open_signup_page(
                            log_callback=wlog, cancel_callback=self.should_stop
                        )
                        wlog("[*] 2. 创建邮箱并提交")
                        email, dev_token = fill_email_and_submit(
                            log_callback=wlog, cancel_callback=self.should_stop
                        )
                        wlog(f"[*] 邮箱: {email}")
                        wlog(f"[Debug] 邮箱 token 已获取 (len={len(str(dev_token or ''))})")
                        try:
                            with open(
                                accounts_side_file("mail_credentials.txt"),
                                "a",
                                encoding="utf-8",
                            ) as f:
                                f.write(f"{email}\t{dev_token}\n")
                        except Exception:
                            pass
                        wlog("[*] 3. 拉取验证码")
                        try:
                            code = fill_code_and_submit(
                                email,
                                dev_token,
                                log_callback=wlog,
                                cancel_callback=self.should_stop,
                            )
                            mail_ok = True
                            break
                        except Exception as mail_exc:
                            msg = str(mail_exc)
                            if ("未收到验证码" in msg or "验证码" in msg) and mail_try < max_mail_retry:
                                wlog(f"[!] 本邮箱未取到验证码，自动更换新邮箱重试: {msg}")
                                finalize_email_provider_claim(
                                    "release",
                                    detail=msg,
                                    log_callback=wlog,
                                )
                                restart_browser(log_callback=wlog)
                                sleep_with_cancel(1, self.should_stop)
                                continue
                            raise

                    if not mail_ok:
                        raise Exception("验证码阶段失败，已达到最大重试次数")
                    wlog(f"[*] 验证码: {code}")
                    wlog("[*] 4. 填写资料")
                    profile = fill_profile_and_submit(
                        log_callback=wlog, cancel_callback=self.should_stop
                    )
                    wlog(f"[*] 资料已填: {profile.get('given_name')} {profile.get('family_name')}")
                    # 资料提交已被页面确认，邮箱从此不可重新注册；SSO 超时改走登录恢复。
                    provider_claim_outcome = "success"
                    provider_claim_detail = "Grok 注册资料已提交，等待获取 SSO"
                    persist_submitted_outlook_account(
                        email,
                        profile,
                        log_callback=wlog,
                    )
                    wlog("[*] 5. 等待 sso cookie")
                    sso = wait_for_sso_cookie(
                        log_callback=wlog, cancel_callback=self.should_stop
                    )
                    cpa_ok = finalize_acquired_sso_account(
                        email,
                        profile.get("password", ""),
                        sso,
                        log_callback=wlog,
                        file_lock=getattr(self, "_accounts_lock", None),
                    )
                    lock = getattr(self, "_stats_lock", None)
                    if lock:
                        with lock:
                            self.results.append({"email": email, "sso": sso, "profile": profile})
                    else:
                        self.results.append({"email": email, "sso": sso, "profile": profile})
                    self._record_success()
                    provider_claim_outcome = "success"
                    provider_claim_detail = "Grok 注册成功并已保存 SSO"
                    retry_count_for_slot = 0
                    i += 1
                    if cpa_ok:
                        wlog(f"[+] 注册成功: {email}")
                    else:
                        wlog(f"[+] 注册成功（SSO 已保存，所选 auth 输出存在失败）: {email}")
                    if (
                        self.success_count > 0
                        and self.success_count % MEMORY_CLEANUP_INTERVAL == 0
                        and i < count
                        and workers <= 1
                    ):
                        cleanup_runtime_memory(
                            log_callback=wlog,
                            reason=f"已成功 {self.success_count} 个账号，执行定期清理",
                        )
                except RegistrationCancelled:
                    if provider_claim_outcome != "success":
                        provider_claim_outcome = "release"
                        provider_claim_detail = "用户停止注册，资料尚未提交"
                    else:
                        provider_claim_detail = "用户停止注册，账号已建号并保留待恢复 SSO"
                    wlog("[!] 注册被用户停止")
                    break
                except icloud_hme_provider.ICloudHMEAddressLimitError as exc:
                    kind = self._record_failure(exc)
                    retry_count_for_slot = 0
                    i += 1
                    # 额度属于账号级上游限制，继续换代理或等待账号间隔没有意义。
                    self.stop_requested = True
                    wlog(
                        f"[-] iCloud HME 创建额度受限 "
                        f"[{FAIL_LABELS.get(kind, kind)}]: {exc}"
                    )
                    wlog("[!] 所有活跃 iCloud 账号当前均不可创建地址，已自动停止整批任务")
                    provider_claim_detail = str(exc)
                except outlook_email_provider.OutlookEmailPoolEmptyError as exc:
                    kind = self._record_failure(exc)
                    retry_count_for_slot = 0
                    i += 1
                    # 邮箱池耗尽属于批次级终止条件，避免后续 worker 继续空轮询。
                    self.stop_requested = True
                    provider_claim_detail = str(exc)
                    wlog(
                        f"[-] OutlookEmail 项目邮箱池已耗尽 "
                        f"[{FAIL_LABELS.get(kind, kind)}]: {exc}"
                    )
                    wlog("[!] 当前项目没有可领取邮箱，已自动停止整批任务")
                except EmailDomainRejected as exc:
                    provider_claim_outcome = "failed"
                    provider_claim_detail = str(exc)
                    kind = self._record_failure(exc)
                    retry_count_for_slot = 0
                    i += 1
                    wlog(f"[-] 邮箱域名被 xAI 拒绝 [{FAIL_LABELS.get(kind, kind)}]: {exc}")
                    wlog("[!] 请更换邮箱提供商或域名（如 Cloudflare 自建域 / MailNest），公共临时域常被拉黑")
                except AccountRetryNeeded as exc:
                    provider_claim_detail = str(exc)
                    retry_count_for_slot += 1
                    if retry_count_for_slot <= max_slot_retry:
                        wlog(
                            f"[!] 当前账号流程卡住，重试第 {retry_count_for_slot}/{max_slot_retry} 次: {exc}"
                        )
                    else:
                        kind = self._record_failure(exc)
                        wlog(
                            f"[-] 当前账号已达到最大重试次数，跳过 [{FAIL_LABELS.get(kind, kind)}]: {exc}"
                        )
                        retry_count_for_slot = 0
                        i += 1
                except Exception as exc:
                    provider_claim_detail = str(exc)
                    kind = self._record_failure(exc)
                    retry_count_for_slot = 0
                    i += 1
                    wlog(f"[-] 注册失败 [{FAIL_LABELS.get(kind, kind)}]: {exc}")
                finally:
                    try:
                        finalize_email_provider_claim(
                            provider_claim_outcome,
                            detail=provider_claim_detail,
                            log_callback=wlog,
                            stopped=self.should_stop(),
                        )
                    except Exception as finalize_exc:
                        wlog(f"[!] 邮箱领取状态结算异常: {finalize_exc}")
                    self.update_stats()
                    if self.should_stop():
                        break
                    # 每轮结束只关浏览器，不立刻再开。
                    # 下一轮 open_signup_page 会按需启动并导航到官网，避免空浏览器残留。
                    if i >= count:
                        continue
                    # 账号间随机间隔
                    wait_sec = parse_account_interval()
                    if wait_sec > 0:
                        wlog(f"[*] 下一个账号前等待 {wait_sec:.0f} 秒...")
                        sleep_with_cancel(wait_sec, self.should_stop)
                    try:
                        stop_browser()
                        time.sleep(0.5)
                    except Exception as close_exc:
                        if self.should_stop():
                            break
                        wlog(f"[Debug] 轮次关闭浏览器失败: {close_exc}")
        except RegistrationCancelled:
            wlog("[!] 注册被用户停止")
        except Exception as exc:
            wlog(f"[!] 任务异常: {exc}")
        finally:
            try:
                maybe_stop_browser(user_stopped=bool(self.stop_requested), log_callback=wlog)
            except BaseException:
                pass
            # 收尾 UI / 汇总只由 _run_registration_entry 负责，避免打印两次


class CliStopController:
    def __init__(self):
        self.stop_requested = False

    def should_stop(self):
        return self.stop_requested

    def stop(self):
        self.stop_requested = True


def cli_log(message):
    """把脱敏后的 CLI 消息写入控制台和本次会话日志。"""
    message = redact_sensitive_text(message)
    if not should_emit_log(message):
        return
    timestamp = datetime.datetime.now().strftime("%H:%M:%S")
    line = f"[{timestamp}] {message}"
    append_session_log(line)
    print(line, flush=True)


def run_registration_cli(count):
    """执行 CLI 注册，并按每轮结果结算当前邮箱提供商的资源状态。"""
    controller = CliStopController()
    prepare_sso_recovery_run()
    try:
        validate_proxy_config()
    except ValueError as proxy_exc:
        cli_log(f"[!] 代理配置无效: {proxy_exc}")
        return
    proxy_batch_id = new_resin_batch_id()

    # 一次 Ctrl+C 可靠置停：SIGINT 处理器直接设停止标志，不依赖异常在
    # curl_cffi C 回调里向上传播（那里 KeyboardInterrupt 会被吞掉，导致
    # 第一次 Ctrl+C 无效、循环继续跑下一个账号）。连按两次 Ctrl+C 时第二次
    # 恢复默认行为强制中断。
    _prev_sigint = signal.getsignal(signal.SIGINT)

    def _on_sigint(signum, frame):
        if controller.should_stop():
            # 第二次：恢复默认并重新抛出，强制中断
            signal.signal(signal.SIGINT, _prev_sigint)
            raise KeyboardInterrupt
        controller.stop()
        cli_log("[!] 收到 Ctrl+C，正在停止（再按一次强制中断）")

    signal.signal(signal.SIGINT, _on_sigint)
    success_count = 0
    fail_count = 0
    fail_stats = empty_fail_stats()
    retry_count_for_slot = 0
    max_slot_retry = 3
    accounts_output_file = ""  # 已改为按邮箱单独保存，不再使用批量文件
    workers = max(1, min(int(config.get("register_workers", 1) or 1), 24, int(count or 1)))
    pool = load_proxy_pool()
    cli_log(f"[*] 终端模式启动，目标数量: {count} | 并发: {workers} | 代理池: {len(pool)}")
    if is_resin_proxy_mode():
        cli_log(
            "[*] Resin 粘性代理: "
            f"Platform={config.get('resin_platform', RESIN_DEFAULT_PLATFORM)}，"
            "每个账号使用独立 Account"
        )
    _cli_interval_raw = str(config.get("account_interval", "0") or "0").strip()
    if _cli_interval_raw and _cli_interval_raw != "0":
        cli_log(f"[*] 账号间注册间隔: {_cli_interval_raw}s")
    _cli_mode_map = {"device_protocol": "协议 Device Flow", "device_browser": "浏览器 Device Flow", "auth_code": "Authorization Code"}
    _cli_mode_label = _cli_mode_map.get(str(config.get("cpa_token_mode", "device_protocol")), "协议 Device Flow")
    _cli_output_names = [
        name
        for name, selected in zip(
            ("CPA", "Grok2API"),
            get_auth_output_selection(),
        )
        if selected
    ]
    _cli_output_detail = f"，输出={'/'.join(_cli_output_names) or '未勾选'}"
    cli_log(
        f"[*] SSO→auth: {'开' if config.get('cpa_auto_add') else '关（仅保存 SSO）'}"
        + (
            f"（{_cli_mode_label}{_cli_output_detail}）"
            if config.get("cpa_auto_add")
            else ""
        )
    )
    # 启动前清理上次崩溃 / 强杀残留的临时 profile 目录
    try:
        _cleanup_stale_profiles(log_callback=cli_log)
    except Exception:
        pass
    try:
        if is_resin_proxy_mode(config):
            _resin_tunnel.ensure(
                config,
                log_callback=cli_log,
            )
        (
            startup_checks,
            startup_resin_generation,
            startup_attempts,
        ) = run_startup_checks_with_xai_retries(
            dict(config),
            proxy_batch_id,
            log_callback=cli_log,
            cancel_callback=controller.should_stop,
        )
        for name, ok, detail in startup_checks:
            # 多次重试的 xAI 结果已逐次记录，仅补充其他连通性检查项。
            if (
                startup_attempts > 1
                and name == _conn.XAI_SIGNUP_CHECK_NAME
            ):
                continue
            cli_log(f"[检查] [{'OK' if ok else 'FAIL'}] {name}: {detail}")
        if _conn.has_blocking_xai_failure(startup_checks):
            last_detail = next(
                (
                    detail
                    for name, ok, detail in startup_checks
                    if name == _conn.XAI_SIGNUP_CHECK_NAME and not ok
                ),
                "未知错误",
            )
            cli_log(
                f"[!] xAI 注册页启动检查连续 "
                f"{startup_attempts or XAI_STARTUP_CHECK_ATTEMPTS} 次失败，"
                f"已停止建号；最后原因: {last_detail}"
            )
            try:
                signal.signal(signal.SIGINT, _prev_sigint)
            except Exception:
                pass
            return
    except RegistrationCancelled:
        cli_log("[*] 启动检查已取消，未进入注册流程")
        try:
            signal.signal(signal.SIGINT, _prev_sigint)
        except Exception:
            pass
        return
    except (
        _resin_tunnel.ResinTunnelConfigError,
        _resin_tunnel.ResinTunnelError,
    ) as exc:
        cli_log(f"[!] Resin SSH 隧道不可用，已停止建号: {exc}")
        try:
            signal.signal(signal.SIGINT, _prev_sigint)
        except Exception:
            pass
        return
    except Exception as exc:
        cli_log(f"[!] 启动连通性检查异常，继续注册: {exc}")
        startup_resin_generation = 0

    def _cli_record_failure(exc):
        nonlocal fail_count
        kind = classify_failure(exc)
        fail_count += 1
        fail_stats[kind] = fail_stats.get(kind, 0) + 1
        return kind

    if workers > 1:
        # CLI 并发：多线程，每线程独立浏览器（thread-local）
        stats_lock = threading.Lock()
        accounts_lock = threading.Lock()
        base, rem = divmod(count, workers)
        chunks = [base + (1 if i < rem else 0) for i in range(workers)]
        threads = []
        shared = {"success": 0, "fail": 0, "fail_stats": empty_fail_stats()}

        def worker(n, wid):
            """执行单个 CLI worker 的注册分片并汇总局部统计。"""
            local_success = 0
            local_fail = 0
            local_fail_stats = empty_fail_stats()
            rotate_idx = 0
            i = 0
            try:
                px, resin_account = bind_proxy_for_account(
                    proxy_batch_id,
                    wid,
                    i,
                    rotate_idx=rotate_idx,
                    resin_generation=(
                        startup_resin_generation
                        if wid == 0 and i == 0
                        else None
                    ),
                )
                if resin_account:
                    cli_log(
                        f"[W{wid+1}] [*] Resin 账号代理已绑定: "
                        f"Platform={config.get('resin_platform', RESIN_DEFAULT_PLATFORM)} "
                        f"Account={resin_account} 入口={redact_proxy(px)}"
                    )
                else:
                    cli_log(
                        f"[W{wid+1}] [*] 绑定代理: {redact_proxy(px) or '直连'}"
                    )
                recover_pending_sso_accounts(
                    log_callback=lambda m: cli_log(f"[W{wid+1}] {m}"),
                    cancel_callback=controller.should_stop,
                )
                try:
                    start_browser(log_callback=lambda m: cli_log(f"[W{wid+1}] {m}"))
                except Exception as boot_exc:
                    # 黑名单/死代理：多换几条 sticky 再放弃
                    booted = False
                    last_boot = boot_exc
                    for _try in range(1, 12):
                        msgb = str(last_boot)
                        if not (
                            "出口IP命中黑名单" in msgb
                            or "无法解析出口 IP" in msgb
                            or "代理不可用或过慢" in msgb
                            or "Failed to get IP" in msgb
                        ):
                            break
                        rotate_idx += 1
                        try:
                            px, resin_account = bind_proxy_for_account(
                                proxy_batch_id,
                                wid,
                                i,
                                rotate_idx=rotate_idx,
                                force_new_resin_lease=is_resin_proxy_mode(),
                            )
                            binding_detail = (
                                f"Resin Account={resin_account}"
                                if resin_account
                                else redact_proxy(px)
                            )
                            cli_log(
                                f"[W{wid+1}] [*] 跳过坏出口，换代理 "
                                f"#{rotate_idx}: {binding_detail} ({msgb[:80]})"
                            )
                            start_browser(log_callback=lambda m: cli_log(f"[W{wid+1}] {m}"))
                            booted = True
                            break
                        except Exception as boot2:
                            last_boot = boot2
                            continue
                    if not booted:
                        local_fail = n
                        local_fail_stats[FAIL_BROWSER] = local_fail_stats.get(FAIL_BROWSER, 0) + n
                        cli_log(f"[W{wid+1}] [-] 浏览器启动失败，{n} 个任务均记为失败: {last_boot}")
                        record_register_result(
                            "fail",
                            kind=FAIL_BROWSER,
                            detail=str(last_boot)[:300],
                            worker=f"W{wid+1}",
                            log_callback=lambda m: cli_log(f"[W{wid+1}] {m}"),
                        )
                        return
                retry = 0
                while i < n and not controller.should_stop():
                    # 邮箱领取后默认释放；只有确认资料已提交才改为成功，永久拒绝才改为失败。
                    provider_claim_outcome = "release"
                    provider_claim_detail = "注册资料尚未确认提交，释放邮箱供下次使用"
                    try:
                        # 同一 i 对应同一个 Resin 槽位，流程重试不会改变粘性身份。
                        bind_proxy_for_account(
                            proxy_batch_id,
                            wid,
                            i,
                            rotate_idx=rotate_idx,
                        )
                        email = ""
                        open_signup_page(
                            log_callback=lambda m: cli_log(f"[W{wid+1}] {m}"),
                            cancel_callback=controller.should_stop,
                        )
                        email, dev_token = fill_email_and_submit(
                            log_callback=lambda m: cli_log(f"[W{wid+1}] {m}"),
                            cancel_callback=controller.should_stop,
                        )
                        code = fill_code_and_submit(
                            email,
                            dev_token,
                            log_callback=lambda m: cli_log(f"[W{wid+1}] {m}"),
                            cancel_callback=controller.should_stop,
                        )
                        profile = fill_profile_and_submit(
                            log_callback=lambda m: cli_log(f"[W{wid+1}] {m}"),
                            cancel_callback=controller.should_stop,
                        )
                        # 资料提交已确认后立即结算邮箱并保存登录恢复凭据。
                        provider_claim_outcome = "success"
                        provider_claim_detail = "Grok 注册资料已提交，等待获取 SSO"
                        persist_submitted_outlook_account(
                            email,
                            profile,
                            log_callback=lambda m: cli_log(f"[W{wid+1}] {m}"),
                        )
                        sso = wait_for_sso_cookie(
                            log_callback=lambda m: cli_log(f"[W{wid+1}] {m}"),
                            cancel_callback=controller.should_stop,
                        )
                        cpa_ok = finalize_acquired_sso_account(
                            email,
                            profile.get("password", ""),
                            sso,
                            log_callback=lambda m: cli_log(f"[W{wid+1}] {m}"),
                            file_lock=accounts_lock,
                        )
                        local_success += 1
                        provider_claim_outcome = "success"
                        provider_claim_detail = "Grok 注册成功并已保存 SSO"
                        i += 1
                        retry = 0
                        if cpa_ok:
                            cli_log(f"[W{wid+1}] [+] 注册成功: {email}")
                        else:
                            cli_log(
                                f"[W{wid+1}] [+] 注册成功"
                                f"（SSO 已保存，所选 auth 输出存在失败）: {email}"
                            )
                        record_register_result(
                            "ok",
                            email,
                            kind="success",
                            detail="auth_output_ok" if cpa_ok else "auth_output_fail",
                            worker=f"W{wid+1}",
                            bot_flag=0,
                            log_callback=lambda m: cli_log(f"[W{wid+1}] {m}"),
                        )
                        # Resin 每个账号天然使用新 Account；普通代理保留原两号轮换策略。
                        if not is_resin_proxy_mode() and local_success % 2 == 0:
                            rotate_idx += 1
                    except RegistrationCancelled:
                        if provider_claim_outcome != "success":
                            provider_claim_outcome = "release"
                            provider_claim_detail = "用户停止注册，资料尚未提交"
                        else:
                            provider_claim_detail = "用户停止注册，账号已建号并保留待恢复 SSO"
                        break
                    except icloud_hme_provider.ICloudHMEAddressLimitError as exc:
                        provider_claim_detail = str(exc)
                        kind = classify_failure(exc)
                        local_fail_stats[kind] = local_fail_stats.get(kind, 0) + 1
                        local_fail += 1
                        i += 1
                        retry = 0
                        # 多 worker 共用停止控制器，首个额度异常会通知其他 worker 收尾。
                        controller.stop()
                        cli_log(
                            f"[W{wid+1}] [-] iCloud HME 创建额度受限 "
                            f"[{FAIL_LABELS.get(kind, kind)}]: {exc}"
                        )
                        cli_log(
                            f"[W{wid+1}] [!] 所有活跃 iCloud 账号当前均不可创建地址，"
                            "已自动停止整批任务"
                        )
                        record_register_result(
                            "fail",
                            email if email else "",
                            kind=kind,
                            detail=str(exc)[:300],
                            worker=f"W{wid+1}",
                            log_callback=lambda m: cli_log(f"[W{wid+1}] {m}"),
                        )
                    except outlook_email_provider.OutlookEmailPoolEmptyError as exc:
                        provider_claim_detail = str(exc)
                        kind = classify_failure(exc)
                        local_fail_stats[kind] = local_fail_stats.get(kind, 0) + 1
                        local_fail += 1
                        i += 1
                        retry = 0
                        controller.stop()
                        cli_log(
                            f"[W{wid+1}] [-] OutlookEmail 项目邮箱池已耗尽 "
                            f"[{FAIL_LABELS.get(kind, kind)}]: {exc}"
                        )
                        cli_log(
                            f"[W{wid+1}] [!] 当前项目没有可领取邮箱，"
                            "已自动停止整批任务"
                        )
                        record_register_result(
                            "fail",
                            email if email else "",
                            kind=kind,
                            detail=str(exc)[:300],
                            worker=f"W{wid+1}",
                            log_callback=lambda m: cli_log(f"[W{wid+1}] {m}"),
                        )
                    except EmailDomainRejected as exc:
                        provider_claim_outcome = "failed"
                        provider_claim_detail = str(exc)
                        kind = classify_failure(exc)
                        local_fail_stats[kind] = local_fail_stats.get(kind, 0) + 1
                        local_fail += 1
                        i += 1
                        retry = 0
                        cli_log(f"[W{wid+1}] [-] 域名拒绝: {exc}")
                        record_register_result(
                            "fail",
                            email if email else "",
                            kind=kind,
                            detail=str(exc)[:300],
                            worker=f"W{wid+1}",
                            log_callback=lambda m: cli_log(f"[W{wid+1}] {m}"),
                        )
                    except AccountRetryNeeded as exc:
                        provider_claim_detail = str(exc)
                        retry += 1
                        if retry > max_slot_retry:
                            kind = classify_failure(exc)
                            local_fail_stats[kind] = local_fail_stats.get(kind, 0) + 1
                            local_fail += 1
                            i += 1
                            retry = 0
                            cli_log(f"[W{wid+1}] [-] 卡住跳过: {exc}")
                    except Exception as exc:
                        provider_claim_detail = str(exc)
                        msg = str(exc)
                        blank_ui = (
                            "inputs=none" in msg
                            or "未找到邮箱输入框" in msg
                            or "页面空白" in msg
                            or "打开注册页后页面空白" in msg
                        )
                        proxy_dead = (
                            "无法解析出口 IP" in msg
                            or "Failed to get IP address" in msg
                            or "代理不可用或过慢" in msg
                            or "出口IP命中黑名单" in msg
                            or "命中黑名单" in msg
                        )
                        turnstile_stuck = (
                            "资料页 Turnstile" in msg
                            or "Turnstile 超时" in msg
                            or "Turnstile 获取 token 失败" in msg
                        )
                        profile_soft = (
                            "资料页表单未就绪" in msg
                            or "资料页无提交按钮" in msg
                            or "资料页提交后未进入登录重定向阶段" in msg
                        )
                        if (blank_ui or proxy_dead or turnstile_stuck or profile_soft) and retry < max_slot_retry:
                            retry += 1
                            why = (
                                "Turnstile卡住"
                                if turnstile_stuck
                                else ("资料页未就绪" if profile_soft else "空页/表单未就绪")
                            )
                            cli_log(
                                f"[W{wid+1}] [!] {why}，同槽位换口重试 {retry}/{max_slot_retry}: {exc}"
                            )
                            rotate_idx += 1
                            continue
                        kind = classify_failure(exc)
                        local_fail_stats[kind] = local_fail_stats.get(kind, 0) + 1
                        local_fail += 1
                        i += 1
                        retry = 0
                        cli_log(f"[W{wid+1}] [-] 失败 [{FAIL_LABELS.get(kind, kind)}]: {exc}")
                        _bf = None
                        _rk = None
                        if kind == FAIL_RISK:
                            import re as _re_f
                            _m = _re_f.search(r"botFlagSource=(\d+)", str(exc))
                            if _m:
                                _bf = int(_m.group(1))
                            _m2 = _re_f.search(r"risk=([\d.]+)", str(exc))
                            if _m2:
                                try:
                                    _rk = float(_m2.group(1))
                                except Exception:
                                    _rk = None
                        # 风控已在 ensure_sso_oauth_eligible 里记过，避免重复
                        if kind != FAIL_RISK:
                            record_register_result(
                                "fail",
                                email or "",
                                kind=kind,
                                detail=str(exc)[:300],
                                worker=f"W{wid+1}",
                                bot_flag=_bf,
                                risk=_rk,
                                log_callback=lambda m: cli_log(f"[W{wid+1}] {m}"),
                            )
                        if kind == FAIL_RISK:
                            rotate_idx += 1
                            if is_resin_proxy_mode():
                                cli_log(
                                    f"[W{wid+1}] [*] 风控拒绝，"
                                    "下一个账号将使用新的 Resin Account"
                                )
                            else:
                                cli_log(
                                    f"[W{wid+1}] [*] 风控拒绝，"
                                    f"切换 sticky #{rotate_idx}"
                                )
                        elif blank_ui or proxy_dead or turnstile_stuck or profile_soft or kind in (
                            FAIL_TURNSTILE,
                            FAIL_PROFILE,
                        ):
                            rotate_idx += 1
                        elif local_success > 0 and local_success % 2 == 0:
                            rotate_idx += 1
                    finally:
                        try:
                            finalize_email_provider_claim(
                                provider_claim_outcome,
                                detail=provider_claim_detail,
                                log_callback=lambda m: cli_log(f"[W{wid+1}] {m}"),
                                stopped=controller.should_stop(),
                            )
                        except Exception as finalize_exc:
                            cli_log(
                                f"[W{wid+1}] [!] 邮箱领取状态结算异常: {finalize_exc}"
                            )
                        if i < n and not controller.should_stop():
                            try:
                                stop_browser()
                                # 冷却：避免热重启立刻撞 SPA 空壳
                                time.sleep(0.5)
                            except Exception:
                                pass
                            try:
                                px, resin_account = bind_proxy_for_account(
                                    proxy_batch_id,
                                    wid,
                                    i,
                                    rotate_idx=rotate_idx,
                                )
                                if resin_account:
                                    cli_log(
                                        f"[W{wid+1}] [*] 下号 Resin Account: "
                                        f"{resin_account} 入口={redact_proxy(px)}"
                                    )
                                else:
                                    cli_log(
                                        f"[W{wid+1}] [*] 下号代理: "
                                        f"{redact_proxy(px) or '直连'}"
                                    )
                                start_browser(log_callback=lambda m: cli_log(f"[W{wid+1}] {m}"))
                                time.sleep(0.5)
                            except Exception as boot_exc:
                                last_boot = boot_exc
                                for _try in range(1, 10):
                                    msgb = str(last_boot)
                                    if not (
                                        "出口IP命中黑名单" in msgb
                                        or "无法解析出口 IP" in msgb
                                        or "代理不可用或过慢" in msgb
                                    ):
                                        break
                                    rotate_idx += 1
                                    try:
                                        # 账号流程可能正在重试，此处只让 Resin 自身故障转移，
                                        # 不强制更换 Account，避免中途改变账号出口身份。
                                        px, resin_account = bind_proxy_for_account(
                                            proxy_batch_id,
                                            wid,
                                            i,
                                            rotate_idx=rotate_idx,
                                        )
                                        binding_detail = (
                                            f"Resin Account={resin_account}"
                                            if resin_account
                                            else redact_proxy(px)
                                        )
                                        cli_log(
                                            f"[W{wid+1}] [*] 下号重试代理 "
                                            f"#{rotate_idx}: {binding_detail}"
                                        )
                                        start_browser(log_callback=lambda m: cli_log(f"[W{wid+1}] {m}"))
                                        time.sleep(0.5)
                                        last_boot = None
                                        break
                                    except Exception as boot2:
                                        last_boot = boot2
                                if last_boot is not None:
                                    cli_log(f"[W{wid+1}] [-] 切换代理后启动失败: {last_boot}")
            finally:
                try:
                    maybe_stop_browser(
                        user_stopped=bool(controller.should_stop()),
                        log_callback=lambda m: cli_log(f"[W{wid+1}] {m}"),
                    )
                except Exception:
                    pass
                with stats_lock:
                    shared["success"] += local_success
                    shared["fail"] += local_fail
                    for k, v in local_fail_stats.items():
                        shared["fail_stats"][k] = shared["fail_stats"].get(k, 0) + v

        for wid, n in enumerate(chunks):
            if n <= 0:
                continue
            t = threading.Thread(target=worker, args=(n, wid), daemon=True)
            t.start()
            threads.append(t)
        for t in threads:
            t.join()
        success_count = shared["success"]
        fail_count = shared["fail"]
        fail_stats = shared["fail_stats"]
        cli_log(
            f"[*] 任务结束。成功 {success_count} | 失败 {fail_count}"
            + (f" | {format_fail_stats(fail_stats)}" if fail_count else "")
        )
        try:
            signal.signal(signal.SIGINT, _prev_sigint)
        except Exception:
            pass
        return

    try:
        i = 0
        px, resin_account = bind_proxy_for_account(
            proxy_batch_id,
            0,
            i,
            resin_generation=startup_resin_generation,
        )
        logged_proxy_index = i
        if resin_account:
            cli_log(
                "[*] Resin 账号代理已绑定: "
                f"Platform={config.get('resin_platform', RESIN_DEFAULT_PLATFORM)} "
                f"Account={resin_account} 入口={redact_proxy(px)}"
            )
        else:
            cli_log(f"[*] 账号代理已绑定: {redact_proxy(px) or '直连'}")
        recover_pending_sso_accounts(
            log_callback=cli_log,
            cancel_callback=controller.should_stop,
        )
        try:
            start_browser(log_callback=cli_log)
        except Exception as boot_exc:
            fail_count += count
            fail_stats[FAIL_BROWSER] = fail_stats.get(FAIL_BROWSER, 0) + count
            cli_log(f"[-] 浏览器启动失败，{count} 个任务均记为失败: {boot_exc}")
            return
        cli_log("[*] 浏览器已启动")
        while i < count:
            if controller.should_stop():
                break
            px, resin_account = bind_proxy_for_account(
                proxy_batch_id,
                0,
                i,
            )
            if logged_proxy_index != i:
                logged_proxy_index = i
                if resin_account:
                    cli_log(
                        "[*] 下一个账号使用新的 Resin 租约: "
                        f"Platform={config.get('resin_platform', RESIN_DEFAULT_PLATFORM)} "
                        f"Account={resin_account} 入口={redact_proxy(px)}"
                    )
                else:
                    cli_log(
                        f"[*] 下一个账号代理: {redact_proxy(px) or '直连'}"
                    )
            cli_log(f"--- 开始第 {i + 1}/{count} 个账号 ---")
            # 邮箱领取后默认释放；只有确认资料已提交才改为成功，永久拒绝才改为失败。
            provider_claim_outcome = "release"
            provider_claim_detail = "注册资料尚未确认提交，释放邮箱供下次使用"
            try:
                email = ""
                dev_token = ""
                code = ""
                mail_ok = False
                max_mail_retry = 3
                for mail_try in range(1, max_mail_retry + 1):
                    cli_log(f"[*] 1. 打开注册页 (尝试 {mail_try}/{max_mail_retry})")
                    open_signup_page(
                        log_callback=cli_log, cancel_callback=controller.should_stop
                    )
                    cli_log("[*] 2. 创建邮箱并提交")
                    email, dev_token = fill_email_and_submit(
                        log_callback=cli_log, cancel_callback=controller.should_stop
                    )
                    cli_log(f"[*] 邮箱: {email}")
                    cli_log(f"[Debug] 邮箱 token 已获取 (len={len(str(dev_token or ''))})")
                    try:
                        with open(
                            accounts_side_file("mail_credentials.txt"),
                            "a",
                            encoding="utf-8",
                        ) as f:
                            f.write(f"{email}\t{dev_token}\n")
                    except Exception:
                        pass
                    cli_log("[*] 3. 拉取验证码")
                    try:
                        code = fill_code_and_submit(
                            email,
                            dev_token,
                            log_callback=cli_log,
                            cancel_callback=controller.should_stop,
                        )
                        mail_ok = True
                        break
                    except Exception as mail_exc:
                        msg = str(mail_exc)
                        if ("未收到验证码" in msg or "验证码" in msg) and mail_try < max_mail_retry:
                            cli_log(f"[!] 本邮箱未取到验证码，自动更换新邮箱重试: {msg}")
                            finalize_email_provider_claim(
                                "release",
                                detail=msg,
                                log_callback=cli_log,
                            )
                            restart_browser(log_callback=cli_log)
                            sleep_with_cancel(1, controller.should_stop)
                            continue
                        raise

                if not mail_ok:
                    raise Exception("验证码阶段失败，已达到最大重试次数")
                cli_log(f"[*] 验证码: {code}")
                cli_log("[*] 4. 填写资料")
                profile = fill_profile_and_submit(
                    log_callback=cli_log, cancel_callback=controller.should_stop
                )
                cli_log(f"[*] 资料已填: {profile.get('given_name')} {profile.get('family_name')}")
                # 资料提交已被页面确认，邮箱从此不可重新注册；SSO 超时改走登录恢复。
                provider_claim_outcome = "success"
                provider_claim_detail = "Grok 注册资料已提交，等待获取 SSO"
                persist_submitted_outlook_account(
                    email,
                    profile,
                    log_callback=cli_log,
                )
                cli_log("[*] 5. 等待 sso cookie")
                sso = wait_for_sso_cookie(
                    log_callback=cli_log, cancel_callback=controller.should_stop
                )
                cpa_ok = finalize_acquired_sso_account(
                    email,
                    profile.get("password", ""),
                    sso,
                    log_callback=cli_log,
                )
                success_count += 1
                provider_claim_outcome = "success"
                provider_claim_detail = "Grok 注册成功并已保存 SSO"
                retry_count_for_slot = 0
                i += 1
                if cpa_ok:
                    cli_log(f"[+] 注册成功: {email}")
                else:
                    cli_log(f"[+] 注册成功（SSO 已保存，所选 auth 输出存在失败）: {email}")
                cli_log(f"[*] 当前统计: 成功 {success_count} | 失败 {fail_count}")
                if success_count > 0 and success_count % MEMORY_CLEANUP_INTERVAL == 0 and i < count:
                    cleanup_runtime_memory(
                        log_callback=cli_log,
                        reason=f"已成功 {success_count} 个账号，执行定期清理",
                    )
            except RegistrationCancelled:
                if provider_claim_outcome != "success":
                    provider_claim_outcome = "release"
                    provider_claim_detail = "用户停止注册，资料尚未提交"
                else:
                    provider_claim_detail = "用户停止注册，账号已建号并保留待恢复 SSO"
                cli_log("[!] 注册被停止")
                break
            except icloud_hme_provider.ICloudHMEAddressLimitError as exc:
                provider_claim_detail = str(exc)
                kind = _cli_record_failure(exc)
                retry_count_for_slot = 0
                i += 1
                controller.stop()
                cli_log(
                    f"[-] iCloud HME 创建额度受限 "
                    f"[{FAIL_LABELS.get(kind, kind)}]: {exc}"
                )
                cli_log("[!] 所有活跃 iCloud 账号当前均不可创建地址，已自动停止整批任务")
            except outlook_email_provider.OutlookEmailPoolEmptyError as exc:
                provider_claim_detail = str(exc)
                kind = _cli_record_failure(exc)
                retry_count_for_slot = 0
                i += 1
                controller.stop()
                cli_log(
                    f"[-] OutlookEmail 项目邮箱池已耗尽 "
                    f"[{FAIL_LABELS.get(kind, kind)}]: {exc}"
                )
                cli_log("[!] 当前项目没有可领取邮箱，已自动停止整批任务")
            except EmailDomainRejected as exc:
                provider_claim_outcome = "failed"
                provider_claim_detail = str(exc)
                kind = _cli_record_failure(exc)
                retry_count_for_slot = 0
                i += 1
                cli_log(f"[-] 邮箱域名被 xAI 拒绝 [{FAIL_LABELS.get(kind, kind)}]: {exc}")
                cli_log("[!] 请更换邮箱提供商或域名（如 Cloudflare 自建域 / MailNest），公共临时域常被拉黑")
            except AccountRetryNeeded as exc:
                provider_claim_detail = str(exc)
                retry_count_for_slot += 1
                if retry_count_for_slot <= max_slot_retry:
                    cli_log(
                        f"[!] 当前账号流程卡住，重试第 {retry_count_for_slot}/{max_slot_retry} 次: {exc}"
                    )
                else:
                    kind = _cli_record_failure(exc)
                    retry_count_for_slot = 0
                    i += 1
                    cli_log(f"[-] 当前账号已达到最大重试次数，跳过 [{FAIL_LABELS.get(kind, kind)}]: {exc}")
            except Exception as exc:
                provider_claim_detail = str(exc)
                kind = _cli_record_failure(exc)
                retry_count_for_slot = 0
                i += 1
                cli_log(f"[-] 注册失败 [{FAIL_LABELS.get(kind, kind)}]: {exc}")
            finally:
                try:
                    finalize_email_provider_claim(
                        provider_claim_outcome,
                        detail=provider_claim_detail,
                        log_callback=cli_log,
                        stopped=controller.should_stop(),
                    )
                except Exception as finalize_exc:
                    cli_log(f"[!] 邮箱领取状态结算异常: {finalize_exc}")
                if controller.should_stop():
                    break
                # 每轮结束只关浏览器，不立刻再开。
                # 下一轮 open_signup_page 会按需启动并导航到官网，避免空浏览器残留。
                if i >= count:
                    continue
                # 账号间随机间隔
                wait_sec = parse_account_interval()
                if wait_sec > 0:
                    cli_log(f"[*] 下一个账号前等待 {wait_sec:.0f} 秒...")
                    _sleep_cancelable(wait_sec, controller.should_stop)
                try:
                    stop_browser()
                    time.sleep(0.5)
                except KeyboardInterrupt:
                    controller.stop()
                    cli_log("[!] 收到 Ctrl+C，正在停止（再按一次强制中断）")
                    break
                except RegistrationCancelled:
                    break
                except Exception as close_exc:
                    if controller.should_stop():
                        break
                    cli_log(f"[Debug] 轮次关闭浏览器失败: {close_exc}")
    except KeyboardInterrupt:
        controller.stop()
        cli_log("[!] 收到 Ctrl+C，正在停止并清理")
    except RegistrationCancelled:
        cli_log("[!] 注册被停止")
    except Exception as exc:
        cli_log(f"[!] 任务异常: {exc}")
    finally:
        try:
            signal.signal(signal.SIGINT, signal.SIG_IGN)
        except Exception:
            pass
        try:
            user_stopped = bool(controller.should_stop())
            if user_stopped and not should_close_browser_after_run(True):
                maybe_stop_browser(user_stopped=True, log_callback=cli_log)
            else:
                cleanup_runtime_memory(log_callback=cli_log, reason="任务结束")
        except BaseException:
            pass
        try:
            cli_log(
                f"[*] 任务结束。成功 {success_count} | 失败 {fail_count}"
                + (f" | {format_fail_stats(fail_stats)}" if fail_count else "")
            )
        except BaseException:
            pass
        try:
            signal.signal(signal.SIGINT, _prev_sigint)
        except Exception:
            pass


def main_cli():
    load_config()
    _wire_runtime_modules()
    count = int(config.get("register_count", 1) or 1)
    if config.get("debug_mode"):
        count = 1
        config["register_workers"] = 1
        cli_log("[*] 调试模式：强制单账号，结束后不关闭浏览器")
    cli_log("[*] CLI 已加载配置")
    cli_log(f"[*] 当前邮箱服务商: {config.get('email_provider', 'duckmail')} | 注册数量: {count}")
    cli_log("[*] 输入 start 后开始；按 Ctrl+C 可强制停止")
    try:
        command = input("> ").strip().lower()
    except KeyboardInterrupt:
        cli_log("[!] 已取消")
        return
    if command != "start":
        cli_log("[!] 未输入 start，已退出")
        return
    try:
        run_registration_cli(count)
    except KeyboardInterrupt:
        # 清理阶段仍可能漏出，保证 CLI 干净退出
        cli_log("[!] 已停止")


def main():
    try:
        initialize_session_log()
    except OSError as exc:
        print(f"[日志] 无法创建日志文件: {exc}", flush=True)
    load_config()
    _wire_runtime_modules()
    if len(sys.argv) > 1 and sys.argv[1].strip().lower() in ("start", "cli", "--cli"):
        main_cli()
        return
    root = tk.Tk()
    setup_light_theme(root)
    app = GrokRegisterGUI(root)
    root.mainloop()


if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        pass

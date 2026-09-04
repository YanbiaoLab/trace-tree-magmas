from __future__ import annotations

import hashlib
import os
import ssl
import tempfile
from dataclasses import dataclass
from pathlib import Path

import certifi
from dotenv import load_dotenv

_SERVICE_ROOT = Path(__file__).resolve().parents[1]
_PACKAGED_CA_CERT = Path(__file__).with_name("sandbox-ca.crt")


@dataclass(frozen=True)
class Settings:
    e2b_api_key: str
    e2b_domain: str
    sandbox_template: str
    sandbox_ca_cert: Path | None
    judge_v3_base_url: str | None
    max_running: int = 200
    create_rate: int = 50
    create_max_attempts: int = 3
    create_backoff_seconds: float = 30.0
    solver_timeout_seconds: int = 3600
    max_judge_calls: int = 20
    request_timeout_seconds: int = 180
    sandbox_user: str = "root"


def load_environment() -> Path | None:
    """Load the service .env without overriding exported variables."""
    explicit = os.environ.get("SOLVER_SANDBOX_ENV_FILE")
    candidates = (
        [Path(explicit).expanduser()] if explicit else [Path.cwd() / ".env", _SERVICE_ROOT / ".env"]
    )
    for candidate in candidates:
        if candidate.is_file():
            load_dotenv(candidate, override=False)
            return candidate.resolve()
    return None


def settings_from_env() -> Settings:
    api_key = os.environ.get("E2B_API_KEY", "").strip()
    domain = os.environ.get("E2B_DOMAIN", "").strip()
    template = os.environ.get("SOLVER_SANDBOX_TEMPLATE", "").strip()
    judge_url = os.environ.get("JUDGE_V3_BASE_URL", "").strip().rstrip("/") or None
    return Settings(
        e2b_api_key=api_key,
        e2b_domain=domain,
        sandbox_template=template,
        sandbox_ca_cert=_resolve_ca_cert(os.environ.get("SOLVER_SANDBOX_CA_CERT")),
        judge_v3_base_url=judge_url,
        max_running=_positive_int("SOLVER_SANDBOX_MAX_RUNNING", 200),
        create_rate=_positive_int("SOLVER_SANDBOX_CREATE_RATE", 50),
        create_max_attempts=_bounded_int(
            "SOLVER_SANDBOX_CREATE_MAX_ATTEMPTS", 3, minimum=1, maximum=10
        ),
        create_backoff_seconds=_bounded_float(
            "SOLVER_SANDBOX_CREATE_BACKOFF_SECONDS", 30.0, minimum=0.0, maximum=3600.0
        ),
        solver_timeout_seconds=_bounded_int(
            "SOLVER_SANDBOX_TIMEOUT_SECONDS", 3600, minimum=1, maximum=3600
        ),
        max_judge_calls=_positive_int("SOLVER_SANDBOX_MAX_JUDGE_CALLS", 20),
        request_timeout_seconds=_positive_int("SOLVER_SANDBOX_REQUEST_TIMEOUT_SECONDS", 180),
        sandbox_user=os.environ.get("SOLVER_SANDBOX_USER", "root").strip() or "root",
    )


def configure_https_trust(custom_ca: Path | None) -> Path | None:
    """Add the Sandbox CA to public roots and expose one process-wide bundle."""
    if custom_ca is None:
        return None
    if not custom_ca.is_file():
        raise FileNotFoundError(f"Sandbox CA certificate not found: {custom_ca}")

    public_bundle = Path(certifi.where()).read_bytes()
    custom_bundle = custom_ca.read_bytes()
    digest = hashlib.sha256(public_bundle + custom_bundle).hexdigest()[:16]
    bundle_dir = Path(tempfile.gettempdir()) / "stage2-solver-sandbox-runner"
    bundle_dir.mkdir(mode=0o700, parents=True, exist_ok=True)
    bundle_path = bundle_dir / f"ca-bundle-{digest}.pem"
    if not bundle_path.exists():
        bundle_path.write_bytes(public_bundle.rstrip() + b"\n" + custom_bundle.rstrip() + b"\n")
        bundle_path.chmod(0o600)

    os.environ["SSL_CERT_FILE"] = str(bundle_path)
    os.environ["REQUESTS_CA_BUNDLE"] = str(bundle_path)
    return bundle_path


def _resolve_ca_cert(configured: str | None) -> Path | None:
    if configured:
        path = Path(configured).expanduser()
        if path.is_absolute():
            return path.resolve()
        for base in (Path.cwd(), _SERVICE_ROOT):
            candidate = base / path
            if candidate.is_file():
                return candidate.resolve()
        return (_SERVICE_ROOT / path).resolve()

    if _PACKAGED_CA_CERT.is_file():
        return _PACKAGED_CA_CERT.resolve()
    return None


def _positive_int(name: str, default: int) -> int:
    return _bounded_int(name, default, minimum=1, maximum=2_147_483_647)


def _bounded_int(name: str, default: int, *, minimum: int, maximum: int) -> int:
    raw = os.environ.get(name)
    if raw is None or not raw.strip():
        return default
    try:
        value = int(raw)
    except ValueError as exc:
        raise ValueError(f"{name} must be an integer") from exc
    if not minimum <= value <= maximum:
        raise ValueError(f"{name} must be between {minimum} and {maximum}")
    return value


def _bounded_float(name: str, default: float, *, minimum: float, maximum: float) -> float:
    raw = os.environ.get(name)
    if raw is None or not raw.strip():
        return default
    try:
        value = float(raw)
    except ValueError as exc:
        raise ValueError(f"{name} must be a number") from exc
    if not minimum <= value <= maximum:
        raise ValueError(f"{name} must be between {minimum} and {maximum}")
    return value


def default_ssl_cert_file() -> str | None:
    """Diagnostic helper used by tests and health tooling."""
    return os.environ.get("SSL_CERT_FILE") or ssl.get_default_verify_paths().cafile

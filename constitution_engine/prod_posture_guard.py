import os
from typing import Tuple

TRUTHY = {"1", "true", "TRUE", "yes", "on"}


def _is_production() -> bool:
    envs = [
        os.getenv("APP_ENV", ""),
        os.getenv("ENV", ""),
        os.getenv("PYTHON_ENV", ""),
    ]
    envs = [e.lower() for e in envs]
    return any(e in ("production", "prod") for e in envs)


def effective_fail_open() -> Tuple[bool, str]:
    """
    Returns (enabled, reason_code). In production, always disabled.
    """
    if _is_production():
        # Normalize/clear for downstream readers
        if os.getenv("ENGINE_FAIL_OPEN") in TRUTHY:
            os.environ["ENGINE_FAIL_OPEN"] = "0"
        return (False, "fail_closed_prod_default")
    # Non-production: respect env flag
    enabled = os.getenv("ENGINE_FAIL_OPEN") in TRUTHY
    return (enabled, "dev_override_enabled" if enabled else "dev_default_disabled")


def enforce():
    """Call once during startup/import to normalize effective posture."""
    enabled, _ = effective_fail_open()
    # No-op here; callers can read effective_fail_open() if they need the bit.
    return enabled


def force_fail_closed_runtime():
    """
    Best-effort: in production, disable any module-level fail-open flags the engine may cache.
    """
    if not _is_production():
        return False
    # normalize env eagerly
    if os.getenv("ENGINE_FAIL_OPEN") in TRUTHY:
        os.environ["ENGINE_FAIL_OPEN"] = "0"
    # Try common module locations/vars without importing heavy deps if missing
    targets = [
        (
            "apps.constitution_engine.engine",
            ["FAIL_OPEN", "ENGINE_FAIL_OPEN", "FAIL_OPEN_ENABLED"],
        ),
        (
            "apps.constitution_engine",
            ["FAIL_OPEN", "ENGINE_FAIL_OPEN", "FAIL_OPEN_ENABLED"],
        ),
        (
            "constitution_engine.engine",
            ["FAIL_OPEN", "ENGINE_FAIL_OPEN", "FAIL_OPEN_ENABLED"],
        ),
    ]
    changed = False
    for mod_name, names in targets:
        try:
            mod = __import__(mod_name, fromlist=["*"])
        except Exception:
            continue
        for name in names:
            if hasattr(mod, name):
                try:
                    setattr(mod, name, False)
                    changed = True
                except Exception:
                    pass
    return changed

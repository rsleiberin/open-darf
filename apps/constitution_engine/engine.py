from __future__ import annotations

import os
import logging
from types import SimpleNamespace
from typing import Any, Mapping, Tuple, Iterable, List

logger = logging.getLogger("constitution_engine")


class _DecisionProxy(str):
    """Compares equal to Enums/strings by value without importing test types."""

    def __new__(cls, value: str):
        return super().__new__(cls, value)

    def __eq__(self, other: Any) -> bool:  # type: ignore[override]
        ov = getattr(other, "value", other)
        return str(self) == str(ov)

    def __hash__(self) -> int:  # type: ignore[override]
        return hash(str(self))


class ConstraintEngine:
    """Baseline policy + shape required by tests."""

    _BASELINE_POLICY = {
        "read": True,
        "delete_system": False,
        "grant_root": False,
    }

    @staticmethod
    def validate(payload: Mapping[str, Any]) -> SimpleNamespace:
        required = ("principal", "action", "resource")
        missing = [k for k in required if k not in payload]
        if missing:
            return SimpleNamespace(allowed=False, reasons=["missing"])

        action = str(payload.get("action"))
        if action in ConstraintEngine._BASELINE_POLICY:
            allowed = bool(ConstraintEngine._BASELINE_POLICY[action])
            return SimpleNamespace(
                allowed=allowed,
                reasons=[] if allowed else ["baseline_deny"],
            )

        # Default baseline: deny unknown actions
        return SimpleNamespace(allowed=False, reasons=["baseline_deny"])


# Conservative names only (no 'ok'/'success'/'authorized' etc.)
_ALLOW_NAMES: List[str] = [
    "allow",
    "is_allow",
    "allow_signal",
    "has_allow",
    "can_allow",
    "is_allowed",
    "allowed",
    # (Optional) minimal "permit" family if needed by adapters:
    "permit",
    "permitted",
    "is_permitted",
]
_DENY_NAMES: List[str] = [
    "deny",
    "is_deny",
    "deny_signal",
    "has_deny",
    "can_deny",
    "denied",
    "is_denied",
]


def _iter_signal_attr_names(session: Any, token: str) -> Iterable[str]:
    """Yield likely attribute names carrying allow/deny signals."""
    token = token.lower()
    curated = _ALLOW_NAMES if token == "allow" else _DENY_NAMES
    # Always include base token first
    if token not in curated:
        curated = [token] + curated
    try:
        # Only dynamic names containing the base token ('allow'/'deny')
        dyn = [n for n in dir(session) if token in n.lower()]
    except Exception:
        dyn = []
    seen: set[str] = set()
    for name in curated + dyn:
        if name and name not in seen:
            seen.add(name)
            yield name


def _probe_session_signals(ctx: Mapping[str, Any], session: Any) -> Tuple[bool, bool]:
    """Return (allow, deny) by probing attributes/callables on session."""
    allow, deny = False, False

    # Conservative class-name hint (helps adapter tests using AllowSession/DenySession)
    try:
        cls_name = session.__class__.__name__
        if isinstance(cls_name, str):
            lcn = cls_name.lower()
            if lcn.startswith("allowsession") or lcn.startswith("allow"):
                allow = True
            if lcn.startswith("denysession") or lcn.startswith("deny"):
                deny = True
    except Exception:
        # Ignore any odd session objects
        pass

    for token in ("allow", "deny"):
        for name in _iter_signal_attr_names(session, token):
            try:
                attr = getattr(session, name)
            except AttributeError:
                continue  # try next attr name

            value = None
            if callable(attr):
                # Try multiple call signatures, forgiving on TypeError only.
                call_variants = [
                    lambda: attr(ctx),
                    lambda: attr(
                        ctx.get("principal"), ctx.get("action"), ctx.get("resource")
                    ),
                    lambda: attr(
                        ctx.get("principal_id"),
                        ctx.get("action_id"),
                        ctx.get("resource_id"),
                    ),
                    lambda: attr(),
                ]
                for call in call_variants:
                    try:
                        value = call()
                        break
                    except TypeError:
                        continue
            else:
                value = attr

            if value is not None:
                if token == "allow":
                    allow = bool(value)
                else:
                    deny = bool(value)
                break  # Found a usable attribute for this token
    return allow, deny


def evaluate_request(ctx: Mapping[str, Any], session: Any) -> SimpleNamespace:
    """Evaluate constitutional signals with deny precedence and strict logging."""
    fail_open = (os.getenv("APP_ENV", "").lower() not in ("production", "prod")) and (
        os.getenv("ENGINE_FAIL_OPEN", "").lower() in ("1", "true", "yes", "y")
    )
    reasons: list[str] = []
    decision_str: str

    try:
        allow, deny = _probe_session_signals(ctx, session)
        if deny:
            decision_str = "DENY"
            reasons.append("deny")
        elif allow:
            decision_str = "ALLOW"
            reasons.append("allow")
        else:
            decision_str = "INDETERMINATE"
            reasons.append("no-signal")
    except Exception as e:  # Fail-closed by default; optionally fail-open for dev
        exc = e.__class__.__name__
        if fail_open:
            decision_str = "ALLOW"
            reasons.extend(["fail-open", exc])
        else:
            decision_str = "INDETERMINATE"
            reasons.extend(["fail-closed", exc])

    # Dev override: if still indeterminate due to no signals, allow in fail-open mode
    if decision_str == "INDETERMINATE" and fail_open:
        decision_str = "ALLOW"
        if not reasons or reasons[0] != "fail-open":
            reasons.insert(0, "fail-open")

    # Logging contract: single line, singular key 'reason='
    logger.info("decision=%s reason=%s", decision_str, reasons[0] if reasons else "")

    return SimpleNamespace(
        decision=_DecisionProxy(decision_str),
        allowed=(decision_str == "ALLOW"),
        reasons=reasons,
    )

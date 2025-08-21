from __future__ import annotations
from apps.constitution_engine.phase2 import Decision, ValidationResult

def decide_precedence(allow_exists: bool, deny_exists: bool) -> ValidationResult:
    """
    Pure precedence rule:
      - If DENY path exists, return DENY with reason code.
      - Else if ALLOW path exists, return ALLOW.
      - Else INDETERMINATE.
    This is DB-free; engine integration will pass the booleans.
    """
    if deny_exists:
        return ValidationResult(Decision.DENY, "deny_precedence:explicit_deny")
    if allow_exists:
        return ValidationResult(Decision.ALLOW, "allow_path:granted")
    return ValidationResult(Decision.INDETERMINATE, "no_policy_match:indeterminate")

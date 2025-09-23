from apps.constitution_engine.prod_posture_guard import (
    enforce as _enforce_prod_posture,
)  # prod fail-closed

_ = _enforce_prod_posture()
# SPDX-License-Identifier: MIT
from .engine import ConstraintEngine  # noqa: E402

__all__ = ["ConstraintEngine"]

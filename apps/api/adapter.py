from __future__ import annotations
from typing import Any, Mapping

from apps.api.dto import ValidationDTO, to_validation_dto
from apps.constitution_engine import engine


def validate(ctx: Mapping[str, Any], neo4j_session) -> ValidationDTO:
    """
    API-edge adapter: evaluates the request via engine and returns a DTO
    suitable for HTTP responses. Fail-closed behavior is enforced in the engine.
    """
    vr = engine.evaluate_request(ctx, neo4j_session)
    return to_validation_dto(vr)

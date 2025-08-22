from fastapi import FastAPI
from pydantic import BaseModel
from apps.api import adapter
from apps.api.receipts import emit as emit_receipt
from apps.observability import metrics

app = FastAPI()


class Req(BaseModel):
    principal_id: str
    action_id: str
    resource_id: str


def get_neo4j_session():
    # Real wiring should inject a Neo4j session (DI). Tests will monkeypatch this.
    raise RuntimeError("Neo4j session not configured")


@app.post("/validate")
def post_validate(req: Req):
    ctx = req.model_dump()
    result = {"decision": "INDETERMINATE", "reason_code": "edge_error:fail_closed"}
    try:
        session = get_neo4j_session()
        result = adapter.validate(ctx, session)
    except Exception:
        # Fail-closed at the edge
        pass
    try:
        emit_receipt(
            decision=result["decision"],
            reason_code=result["reason_code"],
            principal_id=ctx["principal_id"],
            action_id=ctx["action_id"],
            resource_id=ctx["resource_id"],
        )
        metrics.increment("ce.decision", {"decision": result["decision"]})
    except Exception:
        # Observability must not affect behavior
        pass
    return result

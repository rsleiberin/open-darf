from __future__ import annotations
from typing import Any, Callable, Dict, Optional
from apps.hyperrag.guard_scope import guard_call
from apps.constitution_scope.scope import Decision


class GuardedStoreScope:
    """
    Thin wrapper over an underlying store that enforces tri-state scope decisions
    on mutating operations. Read ops pass through. Fail-closed by design.
    """

    def __init__(
        self,
        store: Any,
        rule: Any,
        audit_emit: Optional[Callable[[Dict[str, Any]], None]] = None,
    ):
        self._store = store
        self._rule = rule
        self._audit_emit = audit_emit or (lambda evt: None)

    def _emit(self, op: str, decision: Dict[str, Any], ok: bool, **meta: Any) -> None:
        evt = {"op": op, "ok": ok, "decision": decision, "meta": meta}
        try:
            self._audit_emit(evt)
        except Exception:
            # Never let auditing break the guard or store behaviors.
            pass

    # --- Write operations (guarded) ---

    def put(self, key: Any, value: Any, *, context: Optional[dict] = None) -> bool:
        ok, out, dec = guard_call(
            self._rule, lambda: self._store.put(key, value), context=context
        )
        self._emit("put", dec, ok, key=key)
        return ok

    def delete(self, key: Any, *, context: Optional[dict] = None) -> bool:
        if not hasattr(self._store, "delete"):
            # treat as blocked if op not supported
            self._emit(
                "delete",
                {
                    "decision": Decision.INDETERMINATE,
                    "allow": None,
                    "reason": "not-supported",
                    "meta": {},
                },
                False,
                key=key,
            )
            return False
        ok, out, dec = guard_call(
            self._rule, lambda: self._store.delete(key), context=context
        )
        self._emit("delete", dec, ok, key=key)
        return ok

    # --- Read operations (passthrough) ---

    def get(self, key: Any) -> Any:
        return self._store.get(key)

    def __contains__(self, key: Any) -> bool:
        return key in self._store

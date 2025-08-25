# Scope Taxonomy (Minimal Viable)

**Dimensions**
- **principal.scopes**: list of opaque scope strings (e.g., `["doc:read", "doc:write", "admin:*"]`)
- **action.required_scope**: single scope required to perform the action (e.g., `"doc:read"`)
- **resource.scope_hint** (optional): resource-level suffix or qualifier (e.g., `"org:123"`)

**Semantics**
- Scopes support simple `*` wildcard at the segment level. Example: `admin:*` matches `admin:impersonate`.
- Match rule: A principal is authorized iff **any** principal scope matches the **action.required_scope** (with optional `:<resource.scope_hint>` suffix when provided).
- Decision trace should include `scope_match` or `scope_miss` reason codes.

**Audit Fields**
- `principal.scopes` (array), `action.required_scope` (string), `resource.scope_hint` (string, optional)
- Evaluator emits: `{"authorized": bool, "matched_scope": str|None, "reason_code": str}`

**Performance Target**
- Evaluator is pure-Python and must complete in **< 1 ms p95** for single checks (measured in unit tests).

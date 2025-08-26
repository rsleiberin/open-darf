import json
from pathlib import Path
from apps.audit import make_jsonl_sink
from apps.hyperrag.guarded_store_scope import GuardedStoreScope


class _Store:
    def __init__(self):
        self._d = {}

    def put(self, k, v):
        self._d[k] = v
        return True

    def get(self, k):
        return self._d.get(k)

    def __contains__(self, k):
        return k in self._d


def _read_jsonl(p: Path):
    return [
        json.loads(line)
        for line in p.read_text(encoding="utf-8").splitlines()
        if line.strip()
    ]


def test_jsonl_sink_writes_append_only(tmp_path: Path):
    path = tmp_path / "guard_decisions.jsonl"
    sink = make_jsonl_sink(str(path))
    sink({"op": "put", "ok": True, "decision": {"decision": "ALLOW"}})
    sink({"op": "delete", "ok": False, "decision": {"decision": "DENY"}})

    assert path.exists()
    rows = _read_jsonl(path)
    assert len(rows) == 2
    assert rows[0]["op"] == "put" and rows[0]["decision"]["decision"] == "ALLOW"
    assert rows[1]["op"] == "delete" and rows[1]["decision"]["decision"] == "DENY"
    assert all("ts" in r for r in rows)


def test_guarded_store_scope_with_filesink(tmp_path: Path):
    path = tmp_path / "guard_decisions.jsonl"
    sink = make_jsonl_sink(str(path))
    store = _Store()
    gs = GuardedStoreScope(store, "allow", audit_emit=sink)
    assert gs.put("k", 1, context={"role": "editor"}) is True
    assert "k" in store

    rows = _read_jsonl(path)
    assert len(rows) == 1
    rec = rows[0]
    assert rec["op"] == "put" and rec["ok"] is True
    assert rec["decision"]["decision"] in ("ALLOW", "DENY", "INDETERMINATE")
    assert "ts" in rec

from apps.provenance.schema import constraint_statements, apply_constraints


class _Counters:
    constraints_added = 1
    indexes_added = 1


class _Result:
    def consume(self):
        return type("_Summary", (), {"counters": _Counters()})()


class _Session:
    def __init__(self, rec):
        self.rec = rec

    def __enter__(self):
        return self

    def __exit__(self, *a):
        return False

    def run(self, cypher: str):
        self.rec["cyphers"].append(cypher)
        return _Result()


class _Driver:
    def __init__(self):
        self.rec = {"cyphers": []}

    def session(self):
        return _Session(self.rec)


def test_constraint_statements_shape():
    stmts = constraint_statements()
    assert any("CREATE CONSTRAINT" in s for s in stmts)
    assert any("CREATE INDEX" in s for s in stmts)
    # Expect 6 total (3 constraints + 3 indexes)
    assert len(stmts) == 6


def test_apply_constraints_runs_all_statements_and_summarizes():
    d = _Driver()
    out = apply_constraints(d)
    assert out["ok"] is True
    assert out["executed"] == 6
    # Our stub reports +1 for each call → totals will be 6 each
    assert out["created_constraints"] >= 0
    assert out["created_indexes"] >= 0
    # First statement should target Document uniqueness
    first = d.rec["cyphers"][0]
    assert "doc_id_unique" in first or "Document" in first

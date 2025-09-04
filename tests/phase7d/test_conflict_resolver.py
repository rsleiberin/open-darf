import random, json
from tools.constitutional.reasoning.conflict import PrincipleVote, resolve

def test_deny_precedence():
    v = [PrincipleVote("safety","DENY"), PrincipleVote("sovereignty","ALLOW")]
    d, r = resolve(v)
    assert d == "REJECTED"
    assert r["rule"] == "deny_precedence"
    assert "safety" in r["deny_principles"]

def test_allow_when_no_deny_and_some_allow(monkeypatch):
    monkeypatch.setenv("REASONING_WEIGHTS_JSON", json.dumps({"sovereignty": 2.0}))
    v = [PrincipleVote("sovereignty","ALLOW"), PrincipleVote("transparency","ABSTAIN")]
    d, r = resolve(v)
    assert d == "ACCEPTABLE"
    assert r["rule"] == "allow_weight_mass"
    assert r["allow_mass"] >= 2.0

def test_pending_when_all_abstain_or_pending(monkeypatch):
    monkeypatch.setenv("REASONING_WEIGHTS_JSON", "{}")
    v = [PrincipleVote("x","ABSTAIN"), PrincipleVote("y","PENDING")]
    d, r = resolve(v)
    assert d == "PENDING"
    assert r["rule"] == "no_allow_then_pending"

def test_commutativity_and_idempotence():
    v = [PrincipleVote("p1","ALLOW"), PrincipleVote("p2","ABSTAIN"), PrincipleVote("p1","ALLOW")]
    d1, _ = resolve(v)
    v_shuffled = v[:]
    random.shuffle(v_shuffled)
    d2, _ = resolve(v_shuffled)
    assert d1 == d2 == "ACCEPTABLE"

from scripts.phase7f.propagation import ac3

def test_ac3_simple_satisfiable():
    vars = ["A","B"]
    domains = {"A":[1,2], "B":[1,2]}
    constraints = {
        ("A","B"): lambda a,b: a != b,
        ("B","A"): lambda b,a: a != b
    }
    ok, rev = ac3(vars, domains, constraints)
    assert ok
    assert set(domains["A"]) == {1,2} and set(domains["B"]) == {1,2}

def test_ac3_detects_inconsistency():
    vars = ["A","B"]
    domains = {"A":[1], "B":[1]}
    constraints = {
        ("A","B"): lambda a,b: a != b,
        ("B","A"): lambda b,a: a != b
    }
    ok, rev = ac3(vars, domains, constraints)
    assert not ok

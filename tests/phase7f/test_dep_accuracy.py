from scripts.phase7f.dep_accuracy import cascade_scope, cycle_detect

def test_cascade_scope_simple():
    edges=[("A","B"),("B","C"),("C","D")]
    starts=["B"]
    assert cascade_scope(edges, starts)=={"B","C","D"}

def test_cycle_detect():
    edges=[("X","Y"),("Y","Z"),("Z","X")]
    assert cycle_detect(edges) is True

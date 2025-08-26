from apps.hyperrag.index_sim import IndexSim


def test_index_sim_neighbors_and_fanout():
    facts = [
        ("A", "author_of", "P1"),
        ("A", "author_of", "P2"),
        ("B", "author_of", "P2"),
        ("A", "cites", "P3"),
        ("P2", "cites", "P3"),
    ]
    idx = IndexSim(facts)
    # Role-scoped
    assert sorted(idx.neighbors("A", "author_of")) == ["P1", "P2"]
    assert idx.fanout_count("A", "author_of") == 2
    # Union across roles
    assert sorted(idx.neighbors("A")) == ["P1", "P2", "P3"]
    assert idx.fanout_count("A") == 3
    # Missing safe
    assert idx.neighbors("Z") == []
    assert idx.fanout_count("Z") == 0

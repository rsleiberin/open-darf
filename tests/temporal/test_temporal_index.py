from datetime import datetime
from apps.hyperrag.temporal_index import (
    TemporalSpan,
    TemporalHyperedge,
    temporal_filter,
)


def ts(s):  # helper
    return datetime.fromisoformat(s.replace("Z", "+00:00"))


def test_span_relations():
    a = TemporalSpan(ts("2020-01-01T00:00:00+00:00"), ts("2021-01-01T00:00:00+00:00"))
    b = TemporalSpan(ts("2020-06-01T00:00:00+00:00"), ts("2020-12-01T00:00:00+00:00"))
    c = TemporalSpan(ts("2019-01-01T00:00:00+00:00"), ts("2019-12-31T00:00:00+00:00"))
    assert b.within(a)
    assert a.overlaps(b)
    assert not c.overlaps(b)


def test_temporal_filter_overlap_and_within():
    e1 = TemporalHyperedge(
        "TP53", "BINDS", "BRCA1", TemporalSpan.from_strings("2020-01-01", "2020-06-01")
    )
    e2 = TemporalHyperedge(
        "EGFR",
        "ACTIVATES",
        "RAS",
        TemporalSpan.from_strings("2020-05-01", "2021-01-01"),
    )
    e3 = TemporalHyperedge(
        "BRCA1", "INHIBITS", "TP53", TemporalSpan.from_strings(None, "2019-01-01")
    )
    edges = [e1, e2, e3]

    win = TemporalSpan.from_strings("2020-05-15", "2020-12-31")
    got_overlap = temporal_filter(edges, win, mode="overlap")
    assert {(e.head, e.relation, e.tail) for e in got_overlap} == {
        ("TP53", "BINDS", "BRCA1"),
        ("EGFR", "ACTIVATES", "RAS"),
    }

    got_within = temporal_filter(
        edges, TemporalSpan.from_strings("2020-01-01", "2021-12-31"), mode="within"
    )
    assert {(e.head, e.relation, e.tail) for e in got_within} == {
        ("TP53", "BINDS", "BRCA1"),
        ("EGFR", "ACTIVATES", "RAS"),
    }

from apps.knowledge_graph.temporal_model import parse_timespan


def test_iso_year():
    evs = parse_timespan("2021")
    assert evs and evs[0]["start"] == "2021-01-01" and evs[0]["end"] == "2021-12-31"


def test_iso_month():
    evs = parse_timespan("2021-03")
    assert evs and evs[0]["start"] == "2021-03-01" and evs[0]["end"] == "2021-03-31"


def test_iso_day():
    evs = parse_timespan("2021-03-15")
    assert evs and evs[0]["start"] == "2021-03-15" and evs[0]["end"] == "2021-03-15"


def test_month_day_range():
    evs = parse_timespan("March 15-20, 2021")
    assert evs and evs[0]["start"] == "2021-03-15" and evs[0]["end"] == "2021-03-20"


def test_open_since_until():
    s = parse_timespan("since 2020-05")
    u = parse_timespan("until 2022")
    assert s and s[0]["start"] == "2020-05-01" and s[0]["end"] is None
    assert u and u[0]["start"] is None and u[0]["end"] == "2022-12-31"

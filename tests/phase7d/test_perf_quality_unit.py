from tools.constitutional.reasoning.perf_monitor import PerfStats
from tools.constitutional.reasoning.quality import quality_score
from tools.constitutional.reasoning import ExplanationEngine, ReasoningInput

def test_perfstats_basic():
    ps = PerfStats()
    for ns in [10, 20, 30, 40, 50]:
        ps.record(ns)
    pct = ps.percentiles()
    assert pct["p50"] >= 20 and pct["p95"] <= 50

def test_quality_score_deterministic():
    eng = ExplanationEngine()
    rin = ReasoningInput(decision="ACCEPTABLE", principles=["p1","p2","p3"], rationale="r", evidence_ids=[])
    exp = eng.explain(rin)
    q = quality_score(exp)
    assert 0.5 <= q["score"] <= 1.0
    assert q["principles"] == 3.0

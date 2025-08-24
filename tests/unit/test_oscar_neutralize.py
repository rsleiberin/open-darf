from apps.document_processor.oscar.pipeline import neutralize_preserving_semantics


def test_high_fidelity_neutralization_gender():
    text = "Clearly, the men were the best performers in the study."
    out = neutralize_preserving_semantics(text, "gender_bias", min_fidelity=0.95)
    assert out["candidate"] is not None
    assert out["fidelity"] >= 0.95
    assert out["human_review"] is False


def test_fidelity_gate_requires_threshold():
    text = "Clearly, the men were the best performers in the study."
    out = neutralize_preserving_semantics(text, "gender_bias", min_fidelity=0.999)
    assert out["candidate"] is None or out["fidelity"] < 0.999
    assert out["human_review"] is True

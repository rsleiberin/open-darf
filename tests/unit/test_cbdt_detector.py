import math
from apps.document_processor.cbdt import CBDTBiasDetector, CBDTConfig

TEXT_NEUTRAL = (
    "We present results with methods described and [1] reference. doi:10.1000/xyz"
)
TEXT_METHOD_GAP = (
    "We present results but offer no methodology. It seems obvious this is best."
)
TEXT_GENDERED = (
    "We studied 30 men and 10 women. The men clearly outperformed women in tests."
)


def test_predict_shape_and_keys():
    det = CBDTBiasDetector(config=CBDTConfig(threshold=0.5))
    probs = det.predict(TEXT_NEUTRAL)
    assert set(probs.keys()) == {c.value for c in det.config.categories}
    for p in probs.values():
        assert 0.0 <= p <= 1.0
    # softmax sums approx 1.0
    assert math.isclose(sum(probs.values()), 1.0, rel_tol=1e-5)


def test_methodology_bias_higher_when_no_methods():
    det = CBDTBiasDetector(config=CBDTConfig(threshold=0.33))
    s1 = det.predict(TEXT_NEUTRAL)["methodology_bias"]
    s2 = det.predict(TEXT_METHOD_GAP)["methodology_bias"]
    assert s2 > s1


def test_gender_bias_higher_with_gendered_terms():
    det = CBDTBiasDetector(config=CBDTConfig(threshold=0.33))
    s1 = det.predict(TEXT_NEUTRAL)["gender_bias"]
    s2 = det.predict(TEXT_GENDERED)["gender_bias"]
    assert s2 > s1


def test_flags_respect_threshold():
    det = CBDTBiasDetector(config=CBDTConfig(threshold=0.80))
    out = det.classify(TEXT_METHOD_GAP)
    assert set(out.keys()) == {"scores", "flags"}
    # With high threshold, most flags likely zero
    assert sum(out["flags"].values()) <= 2

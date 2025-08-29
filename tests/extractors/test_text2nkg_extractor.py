from apps.extractors.text2nkg_extractor import extract_relations_simple


def norm(r):
    return (r["subject"], r["relation"], r["object"])


def test_causes_active():
    out = extract_relations_simple("Vitamin C causes scurvy prevention")
    assert out and norm(out[0]) == ("Vitamin C", "causes", "scurvy prevention")


def test_caused_by_passive():
    out = extract_relations_simple("Hypertension is caused by obesity")
    assert out and norm(out[0]) == ("obesity", "causes", "Hypertension")


def test_treats_active():
    out = extract_relations_simple("Aspirin treats fever")
    assert out and norm(out[0]) == ("Aspirin", "treats", "fever")


def test_treated_by_passive():
    out = extract_relations_simple("Pneumonia is treated by antibiotics")
    assert out and norm(out[0]) == ("antibiotics", "treats", "Pneumonia")


def test_associated_with_bidirectional():
    out = extract_relations_simple("Smoking associated with lung cancer")
    pairs = set(map(norm, out))
    assert ("Smoking", "associated with", "lung cancer") in pairs
    assert ("lung cancer", "associated with", "Smoking") in pairs

from apps.hyperrag.extract import RegexEntityExtractor


def test_regex_extractor_basic():
    text = "Alice met ACME Corp in Austin."
    ents = RegexEntityExtractor().extract(text)
    assert len(ents) >= 2
    names = {e.name for e in ents}
    assert "Alice" in names

import re
import pathlib


def read_flags():
    p = pathlib.Path("var/local/testing.env")
    if not p.exists():
        return {}
    text = p.read_text()
    out = {}
    for k in (
        "EXTRACTOR_SCI",
        "EXTRACTOR_BIO",
        "EXTRACTOR_TEXT2NKG",
        "TEMPORAL_GRAPH_MODEL",
    ):
        m = re.search(rf"^export {k}=(\d+)\s*$", text, re.M)
        if m:
            out[k] = int(m.group(1))
    return out


def test_flags_default_zero():
    flags = read_flags()
    for k in (
        "EXTRACTOR_SCI",
        "EXTRACTOR_BIO",
        "EXTRACTOR_TEXT2NKG",
        "TEMPORAL_GRAPH_MODEL",
    ):
        if k in flags:
            assert flags[k] == 0, f"{k} should default to 0"

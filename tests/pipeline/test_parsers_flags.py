import pytest
from apps.pipeline.parse import extract_text


@pytest.mark.parametrize(
    "flag_env,content,hint_on,hint_off",
    [
        ({"PIPELINE_PARSER_PDF": "1"}, b"%PDF-1.7\n...", "pdf", "noop"),
        ({"PIPELINE_PARSER_DOCX": "1"}, b"PK\x03\x04fake", "docx", "noop"),
        (
            {"PIPELINE_PARSER_HTML": "1"},
            b"<!doctype html><html><body>hi</body></html>",
            "html",
            "noop",
        ),
    ],
)
def test_flag_gated_parsers(monkeypatch, flag_env, content, hint_on, hint_off):
    for k, v in flag_env.items():
        monkeypatch.setenv(k, v)
    t, h = extract_text(content, "application/octet-stream")
    assert h == hint_on
    # Turn off flags
    monkeypatch.delenv(list(flag_env.keys())[0], raising=False)
    t2, h2 = extract_text(content, "application/octet-stream")
    assert h2 == hint_off


def test_text_plain_preferred_without_force(monkeypatch):
    monkeypatch.delenv("PIPELINE_FORCE_MIME", raising=False)
    txt = "hello".encode()
    t, h = extract_text(txt, "text/plain")
    assert h == "text" and t == "hello"


def test_force_mime_bypasses_text_plain(monkeypatch):
    monkeypatch.setenv("PIPELINE_FORCE_MIME", "1")
    t, h = extract_text(b"hello", "text/plain")
    assert h == "noop"  # because routing goes to flags, none set → noop

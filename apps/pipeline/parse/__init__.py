"""Parsers that turn bytes -> text."""

import os
from typing import Tuple
from .html import parse_html
from .pdf import parse_pdf
from .docx import parse_docx

_FLAG = {"1", "true", "yes", "on"}


def _on(name: str) -> bool:
    return os.getenv(name, "").strip().lower() in _FLAG


def extract_text(
    doc_bytes: bytes, mime: str = "application/octet-stream"
) -> Tuple[str, str]:
    # Fast-path for plain text
    if mime.startswith("text/") and not _on("PIPELINE_FORCE_MIME"):
        try:
            return doc_bytes.decode("utf-8"), "text"
        except Exception:
            return doc_bytes.decode("latin-1", errors="replace"), "text"

    # HTML (flag: PIPELINE_PARSER_HTML)
    if _on("PIPELINE_PARSER_HTML"):
        text, hint = parse_html(doc_bytes)
        if hint == "html":
            return text, hint

    # PDF (flag: PIPELINE_PARSER_PDF)
    if _on("PIPELINE_PARSER_PDF"):
        text, hint = parse_pdf(doc_bytes)
        if hint == "pdf":
            return text, hint

    # DOCX (flag: PIPELINE_PARSER_DOCX)
    if _on("PIPELINE_PARSER_DOCX"):
        text, hint = parse_docx(doc_bytes)
        if hint == "docx":
            return text, hint

    # Default noop
    return "", "noop"

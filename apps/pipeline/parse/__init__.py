"""Parsers that turn bytes -> text."""

from typing import Tuple


def extract_text(
    doc_bytes: bytes, mime: str = "application/octet-stream"
) -> Tuple[str, str]:
    """Return (text, parser_hint). Stub returns empty text."""
    return "", "noop"

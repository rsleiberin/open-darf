def parse_docx(doc_bytes: bytes):
    # Minimal detection: DOCX is a zip (starts with PK)
    if not doc_bytes.startswith(b"PK"):
        return "", "noop"
    # Stub: no unzip; identify only
    return "", "docx"

def parse_pdf(doc_bytes: bytes):
    # Minimal detection: PDF files usually start with %PDF
    if not doc_bytes.startswith(b"%PDF"):
        return "", "noop"
    # Stub: we don't parse; just identify
    return "", "pdf"

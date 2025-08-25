def parse_html(doc_bytes: bytes):
    head = doc_bytes[:256].lower()
    if b"<html" in head or b"<!doctype html" in head:
        try:
            return doc_bytes.decode("utf-8", errors="replace"), "html"
        except Exception:
            return doc_bytes.decode("latin-1", errors="replace"), "html"
    return "", "noop"

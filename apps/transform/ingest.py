from __future__ import annotations
import argparse
import json
import mimetypes
import os
import sys
import time
import uuid
from pathlib import Path
from typing import List, Dict, Any, Tuple

# Reuse the Manifest builder we just added
from apps.transform.manifest import Span, build_manifest_v1, sha256_hex


# --- CAS (MinIO S3) helper (content-addressed, pointer-only) ---
def _s3():
    import boto3

    endpoint = os.getenv("MINIO_ENDPOINT", "http://localhost:9100")
    access = os.getenv("MINIO_ACCESS_KEY", "minioadmin")
    secret = os.getenv("MINIO_SECRET_KEY", "minioadmin")
    return boto3.client(
        "s3",
        endpoint_url=endpoint,
        aws_access_key_id=access,
        aws_secret_access_key=secret,
    )


def _ensure_bucket():
    s3 = _s3()
    bucket = os.getenv("MINIO_BUCKET", "anchors")
    try:
        s3.head_bucket(Bucket=bucket)
    except Exception:
        s3.create_bucket(Bucket=bucket)
    return bucket


def cas_put_bytes(b: bytes, digest: str | None = None) -> str:
    """
    Store bytes by digest. Returns digest in form 'sha256-<hex>'.
    """
    if digest is None:
        digest = f"sha256-{sha256_hex(b)}"
    assert digest.startswith("sha256-"), "Only sha256 digests supported"
    bucket = _ensure_bucket()
    s3 = _s3()
    key = f"{digest}"
    try:
        # avoid duplicate storage: check if exists
        s3.head_object(Bucket=bucket, Key=key)
        return digest
    except Exception:
        pass
    s3.put_object(Bucket=bucket, Key=key, Body=b)
    return digest


def cas_exists(digest: str) -> bool:
    bucket = _ensure_bucket()
    s3 = _s3()
    try:
        s3.head_object(Bucket=bucket, Key=digest)
        return True
    except Exception:
        return False


# --- Chunking: linebreak v1 (byte-accurate) ---
def chunk_linebreaks(doc: bytes) -> List[Tuple[int, int]]:
    """
    Split on b'\n' producing byte ranges [start,end) covering the entire doc.
    Keeps empty lines as spans (0-length lines become 1-byte spans for '\n').
    """
    spans: List[Tuple[int, int]] = []
    start = 0
    i = 0
    n = len(doc)
    while i < n:
        if doc[i : i + 1] == b"\n":
            spans.append((start, i + 1))
            start = i + 1
        i += 1
    if start < n:
        spans.append((start, n))
    if not spans and n == 0:
        spans = []
    return spans


# --- Draft I/O ---
def _write_draft(draft: Dict[str, Any]) -> Path:
    p = Path("var/drafts")
    p.mkdir(parents=True, exist_ok=True)
    name = f"{int(time.time())}-{uuid.uuid4().hex[:8]}.json"
    out = p / name
    out.write_text(json.dumps(draft, ensure_ascii=False, indent=2))
    return out


# --- MIME detection ---
def detect_mime(path: Path) -> str:
    mt, _ = mimetypes.guess_type(str(path))
    return mt or "application/octet-stream"


# --- Ingest implementation ---
def ingest(
    file_path: str, user_id: str, auth_class: str = "owner", doc_type: str | None = None
) -> Dict[str, Any]:
    fp = Path(file_path)
    doc_bytes = fp.read_bytes()
    mime = doc_type or detect_mime(fp)

    # 1) CAS store source doc
    doc_digest = f"sha256-{sha256_hex(doc_bytes)}"
    cas_put_bytes(doc_bytes, digest=doc_digest)

    # 2) Chunk → Spans (linebreak v1 default)
    spans_ranges = chunk_linebreaks(doc_bytes)
    spans: List[Span] = []
    for i, (s, e) in enumerate(spans_ranges):
        spans.append(
            Span(
                id=f"s{i}",
                start=s,
                end=e,
                loc=None,  # set for PDFs later
                provenance={"auth_class": auth_class, "user_id": user_id},
                lineage=[{"op": "chunker/linebreak-v1", "parent": doc_digest}],
            )
        )

    # 3) Build + CAS store manifest
    manifest_bytes = build_manifest_v1(
        doc_bytes, mime, spans, user_id=user_id, auth_class=auth_class
    )
    manifest_digest = f"sha256-{sha256_hex(manifest_bytes)}"
    cas_put_bytes(manifest_bytes, digest=manifest_digest)

    # 4) Draft (pointer-only)
    draft = {
        "user_id": user_id,
        "status": "ready_for_review",
        "doc_digest": doc_digest,
        "manifest": {"digest": manifest_digest},
        "qdrant_collection": os.getenv("QDRANT_COLLECTION", "anchors"),
        "created_at": int(time.time()),
    }
    draft_path = _write_draft(draft)
    draft["draft_path"] = str(draft_path)
    return draft


# --- CLI ---
def main(argv=None):
    ap = argparse.ArgumentParser(
        description="Ingest a file → CAS + manifest + draft.json (pointer-only)."
    )
    ap.add_argument("--file", required=True, help="Path to source file")
    ap.add_argument("--user", required=True, help="User id")
    ap.add_argument(
        "--auth-class",
        default="owner",
        choices=["owner", "trusted", "untrusted"],
        help="Provenance class",
    )
    ap.add_argument("--doc-type", default=None, help="Override MIME type")
    args = ap.parse_args(argv)

    t0 = time.perf_counter()
    draft = ingest(
        args.file, args.user, auth_class=args.auth_class, doc_type=args.doc_type
    )
    elapsed_ms = (time.perf_counter() - t0) * 1000.0

    # Minimal operator-friendly output
    print(
        json.dumps(
            {"result": "ok", "elapsed_ms": round(elapsed_ms, 2), "draft": draft},
            ensure_ascii=False,
            indent=2,
        )
    )


if __name__ == "__main__":
    sys.exit(main())

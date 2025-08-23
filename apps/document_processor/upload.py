from __future__ import annotations

import hashlib
import io
import mimetypes
import os
from pathlib import Path
from typing import Any, Dict, Optional

# Prefix for object keys; customizable via env
_DEFAULT_PREFIX = os.getenv("UPLOAD_PREFIX", "docs/")

_MD_TYPES = {".md", ".markdown"}


def sha256_hex(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def guess_content_type(path: str, fallback: str = "application/octet-stream") -> str:
    """
    Robust content-type normalization for common doc types.
    """
    suffix = Path(path).suffix.lower()
    if suffix in _MD_TYPES:
        return "text/markdown"
    if suffix == ".json":
        return "application/json"
    if suffix == ".txt":
        return "text/plain"
    if suffix == ".pdf":
        return "application/pdf"
    ctype, _ = mimetypes.guess_type(path)
    return ctype or fallback


def object_name_for(doc_id: str, filename: str, prefix: Optional[str] = None) -> str:
    """
    Build a deterministic object key. We avoid hashing the path so callers can
    locate objects predictably; dedupe is handled by storage semantics.
    """
    key_prefix = prefix if prefix is not None else _DEFAULT_PREFIX
    fname = Path(filename).name
    return f"{key_prefix.rstrip('/')}/{doc_id}/{fname}"


def upload_bytes(
    client: Any,
    bucket: str,
    doc_id: str,
    filename: str,
    data: bytes,
    *,
    content_type: Optional[str] = None,
    prefix: Optional[str] = None,
) -> Dict[str, Any]:
    """
    Upload raw bytes using an injected client that implements:
      put_object(bucket, object_name, data_stream, length, content_type=...)
    Returns a small summary dict (ok/sha256/size/bucket/object/content_type/etag/version_id).
    """
    ctype = content_type or guess_content_type(filename)
    object_name = object_name_for(doc_id, filename, prefix=prefix)
    size = len(data)
    etag = None
    version_id = None

    # Put object via injected client
    result = client.put_object(
        bucket, object_name, io.BytesIO(data), size, content_type=ctype
    )
    # Best-effort result fields
    etag = getattr(result, "etag", None)
    version_id = getattr(result, "version_id", None)

    return {
        "ok": True,
        "sha256": sha256_hex(data),
        "size": size,
        "bucket": bucket,
        "object": object_name,
        "content_type": ctype,
        "etag": etag,
        "version_id": version_id,
    }


def upload_file(
    client: Any,
    bucket: str,
    doc_id: str,
    file_path: str,
    *,
    content_type: Optional[str] = None,
    prefix: Optional[str] = None,
) -> Dict[str, Any]:
    """
    Convenience wrapper around upload_bytes; reads the file and infers content-type if not provided.
    """
    path = Path(file_path)
    data = path.read_bytes()
    return upload_bytes(
        client,
        bucket,
        doc_id,
        path.name,
        data,
        content_type=content_type or guess_content_type(path.name),
        prefix=prefix,
    )

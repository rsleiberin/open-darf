# SPDX-License-Identifier: MIT
from __future__ import annotations
from dataclasses import dataclass
from typing import Optional, Any, Mapping
import base64
import hashlib
import importlib
import os
import time


@dataclass(frozen=True)
class MinioConfig:
    endpoint: str
    access_key: str
    secret_key: str
    secure: bool = False  # http by default; set True for https


class MinioAdapter:
    """
    Thin, DI-friendly wrapper around minio.Minio with:
      - optional dependency (lazy import)
      - exponential backoff retries
      - content-type handling
      - checksum (md5/sha256) forwarding when provided
    """

    def __init__(self, client: Any):
        self._client = client

    @classmethod
    def from_env(cls) -> "MinioAdapter":
        endpoint = os.getenv("MINIO_ENDPOINT")
        access = os.getenv("MINIO_ACCESS_KEY")
        secret = os.getenv("MINIO_SECRET_KEY")
        secure = os.getenv("MINIO_SECURE", "0").strip().lower() in {"1", "true", "yes"}
        if not (endpoint and access and secret):
            raise RuntimeError(
                "MinIO configuration missing (MINIO_ENDPOINT/ACCESS_KEY/SECRET_KEY)."
            )
        try:
            minio_mod = importlib.import_module("minio")
        except Exception as e:
            raise RuntimeError("minio package not available") from e
        client = minio_mod.Minio(
            endpoint, access_key=access, secret_key=secret, secure=secure
        )
        return cls(client)

    def put_object_bytes(
        self,
        bucket: str,
        key: str,
        data: bytes,
        content_type: Optional[str] = None,
        checksums: Optional[Mapping[str, str]] = None,
        max_retries: int = 3,
        base_delay: float = 0.1,
    ) -> Mapping[str, str]:
        """
        Uploads a small object from bytes with retries.
        checksums may include:
          - "md5": hex string (we send as base64 to MinIO)
          - "sha256": hex string (ignored by SDK but returned for provenance)
        Returns a small dict with bucket/key/etag.
        """
        if not isinstance(data, (bytes, bytearray)):
            raise TypeError("data must be bytes")

        # Prepare headers
        headers = {}
        if content_type:
            headers["Content-Type"] = content_type

        # MD5 handling: MinIO expects base64 MD5 of the content
        if checksums and "md5" in checksums:
            try:
                md5_hex = checksums["md5"]
                md5_raw = bytes.fromhex(md5_hex)
                headers["Content-MD5"] = base64.b64encode(md5_raw).decode("ascii")
            except Exception:
                # If provided but malformed, compute ourselves
                md5_raw = hashlib.md5(data).digest()
                headers["Content-MD5"] = base64.b64encode(md5_raw).decode("ascii")
        else:
            md5_raw = hashlib.md5(data).digest()
            headers["Content-MD5"] = base64.b64encode(md5_raw).decode("ascii")

        attempt = 0
        last_exc: Optional[Exception] = None
        while attempt <= max_retries:
            try:
                # put_object requires a stream; minio supports data + length via put_object
                import io

                stream = io.BytesIO(data)
                result = self._client.put_object(
                    bucket_name=bucket,
                    object_name=key,
                    data=stream,
                    length=len(data),
                    content_type=content_type,
                    metadata=None,
                    headers=headers,
                )
                # The MinIO SDK returns an object with etag; keep it if present
                etag = getattr(result, "etag", None)
                return {"bucket": bucket, "key": key, "etag": etag or ""}
            except Exception as e:
                last_exc = e
                if attempt == max_retries:
                    # Map common auth/bucket errors to friendlier messages
                    msg = str(e).lower()
                    if "no such bucket" in msg:
                        raise RuntimeError(
                            f"MinIO: bucket '{bucket}' does not exist"
                        ) from e
                    if "invalid access key id" in msg or "signature" in msg:
                        raise RuntimeError("MinIO: credentials invalid") from e
                    raise
                time.sleep(base_delay * (2**attempt))
                attempt += 1
        # Should not reach here
        raise last_exc or RuntimeError("MinIO: unknown failure")

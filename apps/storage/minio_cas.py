from __future__ import annotations
import hashlib, io, os, typing as t
from dataclasses import dataclass
import boto3
from botocore.config import Config
from botocore.exceptions import ClientError

_ALG = "sha256"

@dataclass(frozen=True)
class CasRef:
    alg: str
    digest: str
    def __str__(self) -> str:
        return f"{self.alg}:{self.digest}"
    @classmethod
    def from_digest(cls, digest: str, alg: str = _ALG) -> "CasRef":
        return cls(alg=alg, digest=digest)

def _key_for(digest: str) -> str:
    return f"{_ALG}/{digest[:2]}/{digest[2:4]}/{digest}"

class MinioCAS:
    def __init__(
        self,
        endpoint: str | None = None,
        access_key: str | None = None,
        secret_key: str | None = None,
        bucket: str | None = None,
        region: str = "us-east-1",
    ) -> None:
        self.endpoint = endpoint or os.environ.get("MINIO_ENDPOINT", "http://localhost:9100")
        self.access_key = access_key or os.environ.get("MINIO_ACCESS_KEY", "minioadmin")
        self.secret_key = secret_key or os.environ.get("MINIO_SECRET_KEY", "minioadmin")
        self.bucket = bucket or os.environ.get("MINIO_BUCKET", "anchors")
        self._s3 = boto3.client(
            "s3",
            endpoint_url=self.endpoint,
            aws_access_key_id=self.access_key,
            aws_secret_access_key=self.secret_key,
            region_name=region,
            config=Config(signature_version="s3v4", retries={"max_attempts": 3, "mode": "standard"}),
        )

    def put_bytes(self, data: bytes, content_type: str | None = None) -> CasRef:
        digest = hashlib.sha256(data).hexdigest()
        ref = CasRef.from_digest(digest)
        key = _key_for(digest)
        if self.exists(ref):
            return ref
        self._s3.put_object(
            Bucket=self.bucket,
            Key=key,
            Body=data,
            ContentType=content_type or "application/octet-stream",
            Metadata={"x-cas-digest": digest, "x-cas-alg": _ALG},
        )
        return ref

    def put_stream(self, stream: io.BufferedReader, *, content_type: str | None = None) -> CasRef:
        return self.put_bytes(stream.read(), content_type=content_type)

    def get_bytes(self, ref: CasRef, *, verify: bool = True) -> bytes:
        key = _key_for(ref.digest)
        obj = self._s3.get_object(Bucket=self.bucket, Key=key)
        b = obj["Body"].read()
        if verify and hashlib.sha256(b).hexdigest() != ref.digest:
            raise ValueError("CAS integrity check failed")
        return b

    def get_stream(self, ref: CasRef, *, chunk_size: int = 8192, verify: bool = True) -> t.Iterator[bytes]:
        key = _key_for(ref.digest)
        obj = self._s3.get_object(Bucket=self.bucket, Key=key)
        body = obj["Body"]
        hasher = hashlib.sha256() if verify else None
        def _gen():
            while True:
                chunk = body.read(chunk_size)
                if not chunk:
                    break
                if hasher:
                    hasher.update(chunk)
                yield chunk
            if hasher and hasher.hexdigest() != ref.digest:
                raise ValueError("CAS integrity check failed")
        return _gen()

    def head(self, ref: CasRef) -> dict:
        key = _key_for(ref.digest)
        meta = self._s3.head_object(Bucket=self.bucket, Key=key)
        return {
            "size": meta["ContentLength"],
            "etag": meta.get("ETag", "").strip('"'),
            "content_type": meta.get("ContentType"),
            "metadata": meta.get("Metadata", {}),
            "version_id": meta.get("VersionId"),
        }

    def exists(self, ref: CasRef) -> bool:
        key = _key_for(ref.digest)
        try:
            self._s3.head_object(Bucket=self.bucket, Key=key)
            return True
        except ClientError as e:
            code = e.response.get("Error", {}).get("Code")
            if code in ("404", "NoSuchKey", "NotFound"):
                return False
            raise

    def delete(self, ref: CasRef, *, hard: bool = False) -> None:
        key = _key_for(ref.digest)
        if hard:
            self._s3.delete_object(Bucket=self.bucket, Key=key)
        else:
            self._s3.put_object_tagging(
                Bucket=self.bucket, Key=key, Tagging={"TagSet": [{"Key": "quarantine", "Value": "true"}]}
            )

    def key_for(self, ref: CasRef) -> str:
        return _key_for(ref.digest)

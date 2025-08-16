from __future__ import annotations
import argparse, json, os, time
from typing import Optional
from apps.validator.neo4j_client import Graph

TARGET_MS = float(os.getenv("VALIDATE_TARGET_MS", "170"))
CAS_L1_DIR = os.getenv("CAS_L1_DIR", "var/cas")

def _s3():
    import boto3  # lazy
    endpoint = os.getenv("MINIO_ENDPOINT", "http://localhost:9100")
    access = os.getenv("MINIO_ACCESS_KEY", "minioadmin")
    secret = os.getenv("MINIO_SECRET_KEY", "minioadmin")
    return boto3.client("s3", endpoint_url=endpoint, aws_access_key_id=access, aws_secret_access_key=secret)

def _l1_path(key: str) -> str:
    # key is content-address (e.g., "sha256-abc..."); safe as filename
    os.makedirs(CAS_L1_DIR, exist_ok=True)
    return os.path.join(CAS_L1_DIR, key)

def _read_manifest_bytes(digest: str) -> tuple[bytes, str]:
    # Try L1 cache first
    p = _l1_path(digest)
    if os.path.exists(p):
        return open(p, "rb").read(), "l1"
    # Fallback to S3, then populate L1
    bucket = os.getenv("MINIO_BUCKET", "anchors")
    s3 = _s3()
    obj = s3.get_object(Bucket=bucket, Key=digest)
    data = obj["Body"].read()
    try:
        with open(p, "wb") as f:
            f.write(data)
    except Exception:
        pass
    return data, "s3"

def _load_json_manifest(digest: str) -> tuple[dict, dict]:
    b, source = _read_manifest_bytes(digest)
    return json.loads(b.decode("utf-8")), {"bytes": len(b), "source": source}

def _write_audit(record: dict):
    os.makedirs("var/audit", exist_ok=True)
    path = os.path.join("var/audit", f"{int(time.time()*1000)}-validation.json")
    with open(path, "w", encoding="utf-8") as f:
        json.dump(record, f, ensure_ascii=False, indent=2)
    return path

def _invariants_ok(draft: dict, manifest: dict) -> bool:
    try:
        assert draft.get("user_id")
        assert draft.get("doc_digest")
        assert draft.get("manifest", {}).get("digest")
        prov = manifest.get("provenance", {})
        assert prov.get("auth_class") in {"owner","trusted","untrusted"}
        assert manifest.get("doc", {}).get("digest") == draft["doc_digest"]
        return True
    except AssertionError:
        return False

def validate(draft_path: str, *, strict: bool=False, mirror_spans: bool=True, max_spans: Optional[int]=None) -> dict:
    t0 = time.perf_counter()
    draft = json.load(open(draft_path, "r", encoding="utf-8"))
    man_digest = draft["manifest"]["digest"]

    t_io_0 = time.perf_counter()
    manifest, io_meta = _load_json_manifest(man_digest)
    t_io_1 = time.perf_counter()

    t_n4j_0 = time.perf_counter()
    with Graph() as g:
        g.mirror_draft(draft=draft, manifest=manifest, mirror_spans=mirror_spans, max_spans=max_spans)
    t_n4j_1 = time.perf_counter()

    inv_ok = _invariants_ok(draft, manifest)
    elapsed_ms = (time.perf_counter() - t0) * 1000.0
    io_ms = (t_io_1 - t_io_0) * 1000.0
    neo4j_ms = (t_n4j_1 - t_n4j_0) * 1000.0
    pass_latency = elapsed_ms <= TARGET_MS

    result = {
        "result": "pass" if inv_ok and (pass_latency or not strict) else "fail",
        "invariants_ok": inv_ok,
        "elapsed_ms": round(elapsed_ms, 2),
        "breakdown_ms": {f"{io_meta.get('source')}_read+json": round(io_ms,2), "neo4j_mirror": round(neo4j_ms,2)},
        "bytes_read": io_meta.get("bytes"),
        "target_ms": TARGET_MS,
        "strict": bool(strict),
        "manifest_digest": man_digest,
        "latency_gate": "ok" if pass_latency else "warn",
    }
    result["audit_path"] = _write_audit(result)
    return result

def main(argv=None):
    ap = argparse.ArgumentParser(description="Validate draft against constitutional gates + Neo4j mirror.")
    ap.add_argument("--draft", required=True, help="Path to draft JSON")
    ap.add_argument("--strict", action="store_true", help="Fail if latency exceeds target")
    ap.add_argument("--no-spans", action="store_true", help="Skip mirroring Span nodes for speed")
    ap.add_argument("--max-spans", type=int, default=None, help="Limit number of Span nodes mirrored")
    args = ap.parse_args(argv)
    mirror_spans = not args.no_spans
    print(json.dumps(validate(args.draft, strict=args.strict, mirror_spans=mirror_spans, max_spans=args.max_spans),
                     ensure_ascii=False, indent=2))

if __name__ == "__main__":
    main()

from __future__ import annotations
import argparse
import json
import os
import boto3


def _s3():
    endpoint = os.getenv("MINIO_ENDPOINT", "http://localhost:9100")
    access = os.getenv("MINIO_ACCESS_KEY", "minioadmin")
    secret = os.getenv("MINIO_SECRET_KEY", "minioadmin")
    return boto3.client(
        "s3",
        endpoint_url=endpoint,
        aws_access_key_id=access,
        aws_secret_access_key=secret,
    )


def _get_json_from_cas(digest: str) -> dict:
    bucket = os.getenv("MINIO_BUCKET", "anchors")
    s3 = _s3()
    b = s3.get_object(Bucket=bucket, Key=digest)["Body"].read()
    return json.loads(b.decode("utf-8"))


def main(argv=None):
    ap = argparse.ArgumentParser(
        description="Show draft summary (manifest + first spans)"
    )
    ap.add_argument("--draft", required=True)
    ap.add_argument("--first", type=int, default=3)
    args = ap.parse_args(argv)

    draft = json.load(open(args.draft, "r", encoding="utf-8"))
    man_digest = draft["manifest"]["digest"]
    m = _get_json_from_cas(man_digest)
    doc_digest = m["doc"]["digest"]
    spans = m.get("spans", [])[: args.first]
    rows = []
    for s in spans:
        uri = f"cas:{doc_digest}#byte={s['start']}-{s['end']}"
        rows.append({"id": s["id"], "start": s["start"], "end": s["end"], "uri": uri})
    print(
        json.dumps(
            {
                "draft_path": args.draft,
                "manifest_digest": man_digest,
                "doc_digest": doc_digest,
                "spans_preview": rows,
            },
            ensure_ascii=False,
            indent=2,
        )
    )


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
import argparse, hashlib, json, os, re, sys
from typing import List, Dict, Any, Iterable, Tuple

HEX64 = re.compile(r"^[0-9a-f]{64}$")
CHUNK = 1024 * 1024

def hash_file(path: str) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        while True:
            chunk = f.read(CHUNK)
            if not chunk:
                break
            h.update(chunk)
    return h.hexdigest()

def collect_fs_digests(root_dir: str) -> List[str]:
    leaves: List[str] = []
    for base, _dirs, files in os.walk(root_dir):
        for fn in files:
            p = os.path.join(base, fn)
            try:
                leaves.append(hash_file(p))
            except Exception as e:
                print(f"[warn] skipping unreadable file: {p} ({e})", file=sys.stderr)
    return leaves

# Prefer these keys if present in a manifest line (any nesting).
PREFERRED_KEYS = {"sha256", "cas_sha256", "digest", "blob_sha256", "content_sha256", "hash"}

def _walk_values(obj: Any) -> Iterable[Tuple[str, str]]:
    if isinstance(obj, dict):
        for k, v in obj.items():
            if isinstance(v, str) and HEX64.match(v):
                yield k, v
            else:
                yield from _walk_values(v)
    elif isinstance(obj, list):
        for x in obj:
            yield from _walk_values(x)

def is_deleted(obj: Dict[str, Any]) -> bool:
    if obj.get("deleted") is True:
        return True
    op = str(obj.get("op") or obj.get("event") or "").lower()
    if "delete" in op:
        return True
    status = str(obj.get("status") or "").lower()
    return status in {"removed", "deleted"}

def collect_manifest_digests(jsonl_path: str, ignore_deleted: bool = True) -> List[str]:
    leaves: List[str] = []
    with open(jsonl_path, "r", encoding="utf-8", errors="ignore") as f:
        for line in f:
            line = line.strip()
            if not line or not line.startswith("{"):
                continue
            try:
                obj = json.loads(line)
            except json.JSONDecodeError:
                continue
            if ignore_deleted and is_deleted(obj):
                continue

            found: Dict[str, str] = {}
            for k, v in _walk_values(obj):
                if HEX64.match(v):
                    found[k] = v

            picked = ""
            for k in PREFERRED_KEYS:
                if k in found:
                    picked = found[k]
                    break
            if not picked and found:
                picked = sorted(found.values())[0]

            if picked:
                leaves.append(picked)
    return leaves

def merkle_root_from_digests(digests: List[str]) -> str:
    if not digests:
        return hashlib.sha256(b"").hexdigest()
    joined = ("\n".join(sorted(digests))).encode("utf-8")
    return hashlib.sha256(joined).hexdigest()

def main():
    ap = argparse.ArgumentParser(description="Compute set-Merkle root from FS or JSONL manifest.")
    g = ap.add_mutually_exclusive_group(required=True)
    g.add_argument("--from-fs", metavar="DIR", help="Directory to hash.")
    g.add_argument("--from-manifest", metavar="JSONL", help="JSONL manifest to read digests from.")
    ap.add_argument("--print-count", action="store_true", help="Also print leaf count.")
    ap.add_argument("--no-ignore-deleted", action="store_true", help="Include deleted items from manifest.")
    args = ap.parse_args()

    if args.from_fs:
        leaves = collect_fs_digests(args.from_fs)
    else:
        leaves = collect_manifest_digests(args.from_manifest, ignore_deleted=not args.no_ignore_deleted)

    root = merkle_root_from_digests(leaves)
    if args.print_count:
        print(f"{root} {len(leaves)}")
    else:
        print(root)

if __name__ == "__main__":
    main()

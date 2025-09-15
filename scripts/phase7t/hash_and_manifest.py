#!/usr/bin/env python3
import argparse, hashlib, json, os, sys, time

CANON_TEXT = "utf8+lf+trim-trailing"

def is_text(path, peek=4096):
    try:
        with open(path, "rb") as f:
            sample = f.read(peek)
        sample.decode("utf-8")
        return True
    except Exception:
        return False

def canon_bytes(b: bytes) -> bytes:
    try:
        s = b.decode("utf-8")
        s = s.replace("\r\n", "\n").replace("\r", "\n")
        s = "\n".join([line.rstrip(" \t") for line in s.split("\n")])
        return s.encode("utf-8")
    except Exception:
        return b  # non-utf8: return as-is

def sha256_bytes(b: bytes) -> str:
    h = hashlib.sha256()
    h.update(b)
    return h.hexdigest()

def file_entry(root, path):
    full = os.path.join(root, path)
    st = os.stat(full)
    with open(full, "rb") as f:
        raw = f.read()
    data = canon_bytes(raw) if is_text(full) else raw
    digest = sha256_bytes(data)
    kind = "text" if is_text(full) else "binary"
    return {
        "path": path,
        "sha256": digest,
        "size": st.st_size,
        "mtime": int(st.st_mtime),
        "kind": kind
    }

def main():
    ap = argparse.ArgumentParser(description="Phase 7T: hash & manifest")
    ap.add_argument("inputs", nargs="+", help="files or directories")
    ap.add_argument("--out", default="var/reports/phase7t/manifest.json")
    args = ap.parse_args()

    root = os.getcwd()
    files = []
    for ip in args.inputs:
        p = os.path.abspath(ip)
        if os.path.isdir(p):
            for dirpath, _, filenames in os.walk(p):
                for fn in filenames:
                    rp = os.path.relpath(os.path.join(dirpath, fn), root)
                    files.append(rp)
        elif os.path.isfile(p):
            files.append(os.path.relpath(p, root))
        else:
            print(f"[warn] skip non-existent: {ip}", file=sys.stderr)

    files = sorted(set(files))
    entries = []
    for rel in files:
        try:
            entries.append(file_entry(root, rel))
        except Exception as e:
            print(f"[warn] failed {rel}: {e}", file=sys.stderr)

    manifest = {
        "schema_version": 1,
        "generated_utc": time.strftime("%Y%m%dT%H%M%SZ", time.gmtime()),
        "canonicalization": CANON_TEXT,
        "entries": entries
    }
    # manifest self-hash over canonical JSON bytes
    enc = json.dumps(manifest, sort_keys=True, separators=(",", ":")).encode("utf-8")
    manifest["manifest_sha256"] = sha256_bytes(enc)

    os.makedirs(os.path.dirname(args.out), exist_ok=True)
    with open(args.out, "w", encoding="utf-8") as f:
        json.dump(manifest, f, indent=2, sort_keys=True)
    print(f"[ok] wrote {args.out}")
    print(f"[info] entries={len(entries)} manifest_sha256={manifest['manifest_sha256'][:12]}")

if __name__ == "__main__":
    main()

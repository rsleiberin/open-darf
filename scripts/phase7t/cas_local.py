#!/usr/bin/env python3
import os, sys, json, hashlib, shutil, time

def canon_text_bytes(raw: bytes) -> bytes:
    # utf8 decode, normalize line endings to \n, trim trailing spaces/tabs, re-encode utf8
    try:
        s = raw.decode("utf-8")
    except Exception:
        # If decoding fails, treat as binary (no transform)
        return raw
    s = s.replace("\r\n", "\n").replace("\r", "\n")
    s = "\n".join([line.rstrip(" \t") for line in s.split("\n")])
    return s.encode("utf-8")

def sha256_path(p: str) -> str:
    h = hashlib.sha256()
    with open(p,'rb') as f:
        for chunk in iter(lambda: f.read(1<<20), b''):
            h.update(chunk)
    return h.hexdigest()

def sha256_bytes(b: bytes) -> str:
    h = hashlib.sha256(); h.update(b); return h.hexdigest()

def main():
    if len(sys.argv)!=4:
        print(f"usage: {sys.argv[0]} MANIFEST CAS_ROOT RECEIPT_JSON", file=sys.stderr)
        sys.exit(2)
    manifest_path, cas_root, receipt_path = sys.argv[1:4]
    with open(manifest_path,'r',encoding='utf-8') as f:
        mf=json.load(f)
    entries = mf.get("entries",[])
    os.makedirs(cas_root, exist_ok=True)

    stored=0; dedup=0; total_bytes=0; stored_bytes=0
    touched=[]

    for e in entries:
        rel=e["path"]; digest=e["sha256"]; size=int(e["size"]); kind=e.get("kind","binary")
        total_bytes += size
        src=os.path.abspath(rel)
        obj=os.path.join(cas_root, digest)

        # Prepare canonicalized content for text; raw bytes for binary
        with open(src,'rb') as f:
            raw=f.read()
        data = canon_text_bytes(raw) if kind=="text" else raw

        # Validate that computed digest matches manifest; otherwise signal drift
        comp = sha256_bytes(data)
        if comp != digest:
            print(f"[fail] digest mismatch vs manifest for {rel} kind={kind} want={digest[:12]} got={comp[:12]}", file=sys.stderr)
            sys.exit(10)

        if os.path.isfile(obj):
            # Verify stored object bytes match digest; if not, refresh with canonicalized data
            if sha256_path(obj) != digest:
                # Overwrite to ensure CAS invariant holds
                with open(obj,'wb') as g:
                    g.write(data)
                if sha256_path(obj) != digest:
                    print(f"[fail] CAS object could not be corrected: {digest}", file=sys.stderr)
                    sys.exit(11)
            dedup += 1
        else:
            with open(obj,'wb') as g:
                g.write(data)
            if sha256_path(obj) != digest:
                print(f"[fail] post-write CAS hash mismatch for {rel}", file=sys.stderr)
                sys.exit(12)
            stored += 1
            stored_bytes += size

        touched.append({"digest":digest,"path":rel,"cas_obj":obj,"size":size,"kind":kind})

    rec={
        "schema_version":1,
        "phase":"7T",
        "action":"cas_local_store",
        "timestamp_utc":time.strftime("%Y%m%dT%H%M%SZ", time.gmtime()),
        "provenance":{"algorithm":"sha256","canonicalization":"utf8+lf+trim-trailing"},
        "links":[{"rel":"manifest","path":manifest_path},{"rel":"cas_root","path":cas_root}],
        "status":"ok",
        "details":{
            "objects_total":len(entries),
            "bytes_total": total_bytes,
            "stored_new": stored,
            "stored_bytes": stored_bytes,
            "dedup_hits": dedup,
            "touched": touched[:50]
        }
    }
    os.makedirs(os.path.dirname(receipt_path), exist_ok=True)
    with open(receipt_path,'w',encoding='utf-8') as f:
        json.dump(rec,f,indent=2,sort_keys=True)
    print(f"[ok] local CAS: objects_total={len(entries)} stored_new={stored} dedup_hits={dedup} -> {receipt_path}")

if __name__=="__main__":
    main()

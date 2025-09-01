#!/usr/bin/env python3
import argparse
import json
import os
import sys
import hashlib
import tarfile
import tempfile
import shutil
import glob
import urllib.parse
import subprocess

SOURCES_PATH = "datasets/sources.json"

DEFAULT_SOURCES = {
    "scierc": {
        "type": "tar.gz",
        "candidates": [
            {
                "url": "http://nlp.cs.washington.edu/sciIE/data/sciERC_processed.tar.gz",
                "sha256": None,
                "notes": "UW processed",
            },
            {
                "url": "https://ai2-s2-research.s3-us-west-2.amazonaws.com/scierc/scierc.tar.gz",
                "sha256": None,
                "notes": "AI2 mirror (may 403)",
            },
            {
                "url": "https://s3-us-west-2.amazonaws.com/ai2-s2-research/scierc.tar.gz",
                "sha256": None,
                "notes": "AI2 mirror alt (may 403)",
            },
        ],
        "pinned": None,
    },
    "biored": {
        "type": "jsonl",
        "candidates": [
            {
                "url": "https://ftp.ncbi.nlm.nih.gov/pub/lu/BioRED/BioRED.jsonl",
                "sha256": None,
                "notes": "NCBI (may 404)",
            },
            {
                "url": "https://ftp.ncbi.nlm.nih.gov/pub/lu/biored/BioRED.jsonl",
                "sha256": None,
                "notes": "NCBI alt (may 404)",
            },
            {
                "url": "https://nlp.cs.washington.edu/sciIE/data/BioRED.jsonl",
                "sha256": None,
                "notes": "UW mirror (may 404)",
            },
        ],
        "pinned": None,
    },
}


def sha256_file(path, buf=1024 * 1024):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        while True:
            b = f.read(buf)
            if not b:
                break
            h.update(b)
    return h.hexdigest()


def load_sources():
    if os.path.isfile(SOURCES_PATH):
        with open(SOURCES_PATH) as f:
            return json.load(f)
    else:
        return None


def save_sources(obj):
    os.makedirs(os.path.dirname(SOURCES_PATH), exist_ok=True)
    with open(SOURCES_PATH, "w") as f:
        json.dump(obj, f, indent=2)


def ensure_sources():
    cur = load_sources()
    if not cur:
        cur = DEFAULT_SOURCES
        save_sources(cur)
        print(f"WROTE {SOURCES_PATH} (init)")
    else:
        print(f"FOUND {SOURCES_PATH}")
    return cur


def human(n):
    for u in ["B", "KB", "MB", "GB", "TB"]:
        if n < 1024:
            return f"{n:.1f} {u}"
        n /= 1024
    return f"{n:.1f} PB"


def fetch_url(url, dest):
    # prefer curl, fallback to wget
    cmd = None
    if shutil.which("curl"):
        cmd = [
            "bash",
            "-lc",
            f"curl -fL --retry 3 --retry-delay 2 -o {shlex(dest)} {shlex(url)}",
        ]
    elif shutil.which("wget"):
        cmd = ["bash", "-lc", f"wget -O {shlex(dest)} {shlex(url)}"]
    else:
        raise RuntimeError("Neither curl nor wget found.")
    try:
        subprocess.check_call(cmd)
        return True
    except Exception:
        return False


def shlex(s):  # minimal
    return "'" + s.replace("'", "'\\''") + "'"


def stage_scierc(archive_path, out_dir, receipts):
    tmp = tempfile.mkdtemp()
    try:
        with tarfile.open(archive_path, "r:gz") as tar:
            tar.extractall(tmp)
        # locate processed JSONs
        candidates = [
            "scierc_data/processed_data/json",
            "processed_data/json",
            "scierc/processed_data/json",
        ]
        json_dir = None
        for c in candidates:
            p = os.path.join(tmp, c)
            if os.path.isdir(p):
                json_dir = p
                break
        if not json_dir:
            raise RuntimeError("processed_data/json not found in archive")
        os.makedirs(out_dir, exist_ok=True)
        for name in ["train.json", "dev.json", "test.json"]:
            src = os.path.join(json_dir, name)
            if not os.path.isfile(src):
                raise RuntimeError(f"missing {name} in {json_dir}")
            shutil.copy2(src, os.path.join(out_dir, name))
        # manifest
        mani = {"name": "SciERC", "source": "archive", "files": {}}
        for name in ["train.json", "dev.json", "test.json"]:
            p = os.path.join(out_dir, name)
            mani["files"][name] = {
                "sha256": sha256_file(p),
                "bytes": os.path.getsize(p),
            }
        with open(os.path.join(out_dir, "MANIFEST.json"), "w") as f:
            json.dump(mani, f, indent=2)
        print(
            json.dumps(
                {
                    "staged": "scierc",
                    "out_dir": out_dir,
                    "files": list(mani["files"].keys()),
                }
            )
        )
        return True
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


def stage_biored(jsonl_path, out_dir):
    # If official JSONL found, store as single-file manifest.
    os.makedirs(out_dir, exist_ok=True)
    dest = os.path.join(out_dir, "BioRED.jsonl")
    shutil.copy2(jsonl_path, dest)
    mani = {
        "name": "BioRED",
        "source": "jsonl",
        "files": {
            "BioRED.jsonl": {
                "sha256": sha256_file(dest),
                "bytes": os.path.getsize(dest),
            }
        },
    }
    with open(os.path.join(out_dir, "MANIFEST.json"), "w") as f:
        json.dump(mani, f, indent=2)
    print(
        json.dumps({"staged": "biored", "out_dir": out_dir, "files": ["BioRED.jsonl"]})
    )
    return True


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument(
        "--init", action="store_true", help="write default sources.json if absent"
    )
    ap.add_argument("--task", choices=["scierc", "biored"], help="dataset to fetch")
    ap.add_argument("--out", required=False, default=None, help="output directory")
    ap.add_argument(
        "--verify",
        action="store_true",
        help="enforce checksum if present in sources.json",
    )
    args = ap.parse_args()

    if args.init:
        ensure_sources()

    if not args.task:
        return 0

    out_dir = args.out or f"data/{args.task}"
    os.makedirs(out_dir, exist_ok=True)
    sources = ensure_sources()
    meta = sources.get(args.task)
    if not meta:
        print(f"[ERROR] task {args.task} not in sources", file=sys.stderr)
        return 2
    cands = meta.get("candidates", [])

    # If already present locally, compute checksums and pin to local
    if args.task == "scierc" and all(
        os.path.isfile(os.path.join(out_dir, f))
        for f in ("train.json", "dev.json", "test.json")
    ):
        # pin local copy
        pinned = {"url": f"local://{out_dir}", "sha256": None, "notes": "local present"}
        sources[args.task]["pinned"] = pinned
        save_sources(sources)
        print(
            json.dumps(
                {"task": args.task, "status": "local-present", "out_dir": out_dir}
            )
        )
        return 0
    if args.task == "biored" and (
        os.path.isfile(os.path.join(out_dir, "BioRED.jsonl"))
        or glob.glob(os.path.join(out_dir, "*.jsonl"))
    ):
        pinned = {"url": f"local://{out_dir}", "sha256": None, "notes": "local present"}
        sources[args.task]["pinned"] = pinned
        save_sources(sources)
        print(
            json.dumps(
                {"task": args.task, "status": "local-present", "out_dir": out_dir}
            )
        )
        return 0

    # Try candidates
    tmp = tempfile.mkdtemp()
    try:
        ok = False
        used = None
        dl_path = None
        for cand in cands:
            url = cand["url"]
            fn = os.path.basename(urllib.parse.urlparse(url).path) or f"{args.task}"
            dl_path = os.path.join(tmp, fn)
            print(json.dumps({"try": url}))
            # download via shell tools to leverage retries
            if shutil.which("curl"):
                cmd = [
                    "bash",
                    "-lc",
                    f"curl -fL --retry 3 --retry-delay 2 -o {shlex(dl_path)} {shlex(url)}",
                ]
            elif shutil.which("wget"):
                cmd = ["bash", "-lc", f"wget -O {shlex(dl_path)} {shlex(url)}"]
            else:
                print("[ERROR] Neither curl nor wget available", file=sys.stderr)
                return 2
            rc = subprocess.call(cmd)
            if rc != 0:
                continue
            # size & checksum
            sz = os.path.getsize(dl_path)
            h = sha256_file(dl_path)
            if (
                args.verify
                and cand.get("sha256")
                and cand["sha256"].lower() != h.lower()
            ):
                print(
                    json.dumps(
                        {
                            "warning": "checksum-mismatch",
                            "expected": cand["sha256"],
                            "actual": h,
                            "url": url,
                        }
                    )
                )
                continue
            used = {"url": url, "sha256": h, "bytes": sz}
            ok = True
            break
        if not ok:
            print(
                json.dumps({"error": "all-sources-failed", "task": args.task}),
                file=sys.stderr,
            )
            return 3

        # Stage
        if args.task == "scierc":
            stage_scierc(dl_path, out_dir, None)
        else:
            stage_biored(dl_path, out_dir)

        # Pin
        sources[args.task]["pinned"] = used
        save_sources(sources)
        print(json.dumps({"task": args.task, "pinned": used, "out_dir": out_dir}))
        return 0
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


if __name__ == "__main__":
    main()

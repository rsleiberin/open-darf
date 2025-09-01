#!/usr/bin/env python3
import argparse
import json
import sys
from pathlib import Path

REG_PATH = Path("models/model_registry.json")


def load_registry():
    if not REG_PATH.exists():
        print("ERROR: model_registry.json missing", file=sys.stderr)
        sys.exit(2)
    with open(REG_PATH) as f:
        return json.load(f)


def cache_has_model(cache_dir: Path) -> bool:
    if not cache_dir.exists():
        return False
    # Heuristic: any of these files mark a complete weight snapshot
    markers = ["model.safetensors", "pytorch_model.bin"]
    for m in markers:
        if list(cache_dir.rglob(m)):
            return True
    # tokenizers/configs alone don't count
    return False


def ensure_deps():
    try:
        import huggingface_hub  # noqa
    except Exception:
        print("Installing deps: huggingface_hub transformers tokenizers", flush=True)
        import subprocess
        import sys as _sys

        subprocess.check_call(
            [
                _sys.executable,
                "-m",
                "pip",
                "install",
                "-q",
                "huggingface_hub",
                "transformers",
                "tokenizers",
            ]
        )
    # lazy import after potential install
    from huggingface_hub import snapshot_download  # noqa

    return True


def hf_snapshot(repo_id: str, local_dir: Path):
    from huggingface_hub import snapshot_download

    local_dir.mkdir(parents=True, exist_ok=True)
    # download to project-local cache (no symlinks to home cache)
    snapshot_download(
        repo_id=repo_id,
        local_dir=str(local_dir),
        local_dir_use_symlinks=False,
        ignore_patterns=["*.msgpack.index", "*.ot"],
        resume_download=True,
    )


def approx_size_mb(path: Path) -> int:
    total = 0
    for p in path.rglob("*"):
        if p.is_file():
            try:
                total += p.stat().st_size
            except Exception:
                pass
    return int(total / (1024 * 1024))


def cmd_ensure(model_name: str):
    reg = load_registry()
    if model_name not in reg:
        print(f"ERROR: unknown model '{model_name}'", file=sys.stderr)
        sys.exit(2)
    meta = reg[model_name]
    repo_id = meta["hf_id"]
    cache_dir = Path(meta["cache_dir"])
    print(
        json.dumps(
            {
                "action": "ensure",
                "model": model_name,
                "hf_id": repo_id,
                "cache_dir": str(cache_dir),
            },
            indent=2,
        )
    )

    if cache_has_model(cache_dir):
        print(
            f"OK: found cached weights in {cache_dir} (~{approx_size_mb(cache_dir)} MB)"
        )
        return 0

    ensure_deps()
    print(
        f"Downloading {repo_id} → {cache_dir} (est. {meta.get('approx_size_mb','?')} MB)...",
        flush=True,
    )
    hf_snapshot(repo_id, cache_dir)
    print(f"DONE: cached to {cache_dir} (~{approx_size_mb(cache_dir)} MB)")
    return 0


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("model", help="model key in registry (e.g., scibert, biobert)")
    ap.add_argument(
        "--ensure", action="store_true", help="ensure model is cached locally"
    )
    args = ap.parse_args()
    if args.ensure:
        return sys.exit(cmd_ensure(args.model))
    else:
        print("No action. Use --ensure.", file=sys.stderr)
        return sys.exit(2)


if __name__ == "__main__":
    main()

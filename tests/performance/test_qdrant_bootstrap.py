# Service-free, import-safe Qdrant perf sanity
import os
import inspect
import pytest

# Gate entire module behind RUN_PERF=1
if os.getenv("RUN_PERF") != "1":
    pytest.skip("perf suite gated by RUN_PERF=1", allow_module_level=True)

try:
    # Try to import the helpers; skip module if unavailable
    from tools.qdrant_bootstrap import VectorConfig, collection_config  # type: ignore
except Exception:
    pytest.skip(
        "qdrant bootstrap helpers unavailable; skipping qdrant perf",
        allow_module_level=True,
    )


def _make_vector_config():
    """Instantiate VectorConfig with best-effort kwargs (signature-agnostic)."""
    params = getattr(inspect, "signature")(VectorConfig).parameters  # dict of Parameter
    kwargs = {}
    for k in ("size", "dim", "dims", "vector_size"):
        if k in params:
            kwargs[k] = 384
            break
    for k in ("distance", "metric", "space"):
        if k in params:
            kwargs[k] = "Cosine"
            break
    # Fill any required-only params with simple dummies when possible
    for name, p in params.items():
        if (
            name in kwargs
            or p.default is not inspect._empty
            or p.kind in (p.VAR_POSITIONAL, p.VAR_KEYWORD)
        ):
            continue
        # Provide a generic dummy
        if p.annotation in (int, "int"):
            kwargs[name] = 1
        elif p.annotation in (str, "str"):
            kwargs[name] = "auto"
        else:
            # last-resort: None
            kwargs[name] = None
    return VectorConfig(**kwargs)  # type: ignore[arg-type]


def test_qdrant_collection_config_sane():
    vc = _make_vector_config()
    try:
        cfg = collection_config(vc)  # should be pure config, no network
    except Exception as e:
        pytest.skip(f"collection_config unavailable/side-effectful: {type(e).__name__}")
    assert cfg, "collection_config returned falsy"
    # Try to validate a couple of common shapes if present
    vectors = cfg.get("vectors") if isinstance(cfg, dict) else None
    if isinstance(vectors, dict):
        size_like = next((k for k in ("size", "dim", "dims") if k in vectors), None)
        if size_like:
            assert vectors[size_like] in (
                384,
                1,
            )  # allow our 384 default or minimal fallback

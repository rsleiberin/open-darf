import importlib.util
import pytest

if importlib.util.find_spec("fastapi") is None:
    pytest.skip(
        "FastAPI not installed; skipping API route tests in service-free CI",
        allow_module_level=True,
    )

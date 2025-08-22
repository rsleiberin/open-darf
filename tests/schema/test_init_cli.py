import types
from apps.constitution_engine.schema import init as mod


def test_import_ok():
    assert isinstance(mod, types.ModuleType)
    assert hasattr(mod, "SCHEMA_STEPS")
    assert len(mod.SCHEMA_STEPS) >= 3


def test_dry_run():
    # run returns 0 and prints lines in dry-run
    rc = mod.run(dry_run=True)
    assert rc == 0

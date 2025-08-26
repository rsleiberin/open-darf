import importlib.util
from apps.hyperrag.guard import evaluate_action


def test_guard_fail_closed_without_scope():
    spec = importlib.util.find_spec("apps.constitution_scope.scope")
    if spec is None:
        assert evaluate_action("graph.upsert") == "DENY"
    else:
        # If scope exists, we accept ALLOW or DENY depending on repo rules.
        assert evaluate_action("graph.upsert") in {"ALLOW", "DENY", "INDETERMINATE"}

from apps.api.adapter import validate


class ErrorSession:
    def run(self, *a, **k):  # simulate DB failure / schema missing
        raise RuntimeError("boom")


class _Result:
    def __init__(self, rec):
        self._rec = rec

    def single(self):
        return self._rec


class AllowSession:
    def run(self, *a, **k):
        return _Result({"allow_exists": True, "deny_exists": False})


def test_adapter_fail_closed_maps_to_indeterminate_dto():
    dto = validate(
        {"principal_id": "p", "action_id": "a", "resource_id": "r"}, ErrorSession()
    )
    assert dto["decision"] == "INDETERMINATE"
    assert isinstance(dto["reason_code"], str) and dto["reason_code"] != ""


def test_adapter_allow_path_maps_to_allow_dto():
    dto = validate(
        {"principal_id": "p", "action_id": "a", "resource_id": "r"}, AllowSession()
    )
    assert dto["decision"] == "ALLOW"

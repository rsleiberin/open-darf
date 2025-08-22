from apps.constitution_engine.reason_codes import KNOWN_REASON_CODES


def test_reason_code_catalogue_includes_required():
    required = {
        "deny_precedence:explicit_deny",
        "allow_path:granted",
        "neo4j_schema_missing:fail_closed",
        "fail_open:dev_override",
        "edge_error:fail_closed",
    }
    assert required.issubset(KNOWN_REASON_CODES)

from pathlib import Path

from apps.document_processor.upload import (
    guess_content_type,
    object_name_for,
    sha256_hex,
    upload_bytes,
    upload_file,
)


class _StubResult:
    etag = "stub-etag"
    version_id = "v1"


class _StubClient:
    def __init__(self, recorder):
        self.rec = recorder

    def put_object(self, bucket, object_name, data_stream, length, content_type=None):
        payload = data_stream.read()
        # Record call details
        self.rec["bucket"] = bucket
        self.rec["object"] = object_name
        self.rec["content_type"] = content_type
        self.rec["length"] = length
        self.rec["bytes"] = payload
        # Validate length correctness
        assert len(payload) == length
        return _StubResult()


def test_guess_content_type_priority_map():
    assert guess_content_type("notes.md") == "text/markdown"
    assert guess_content_type("data.json") == "application/json"
    assert guess_content_type("file.pdf") == "application/pdf"
    assert guess_content_type("unknown.weird") == "application/octet-stream"


def test_object_name_for_doc_prefix_and_filename():
    key = object_name_for("doc123", "report.md", prefix="docs/")
    assert key == "docs/doc123/report.md"


def test_upload_bytes_records_correct_fields_and_hash():
    rec = {}
    client = _StubClient(rec)
    data = b"hello world"
    out = upload_bytes(client, "bucketA", "docX", "note.md", data)
    assert out["ok"] is True
    assert out["bucket"] == "bucketA"
    assert out["object"].endswith("/docX/note.md") or out["object"].endswith(
        "docX/note.md"
    )
    assert out["content_type"] == "text/markdown"
    assert out["sha256"] == sha256_hex(data)
    assert out["etag"] == "stub-etag"
    assert out["version_id"] == "v1"
    # Ensure stub saw the same values
    assert rec["content_type"] == "text/markdown"
    assert rec["length"] == len(data)


def test_upload_file_reads_and_infers_type(tmp_path: Path):
    tmp = tmp_path / "sample.json"
    tmp.write_bytes(b"{}")
    rec = {}
    client = _StubClient(rec)
    out = upload_file(client, "buck", "docY", str(tmp))
    assert out["content_type"] == "application/json"
    assert out["object"].endswith("/docY/sample.json") or out["object"].endswith(
        "docY/sample.json"
    )

from apps.document_processor.minio_adapter import MinioAdapter


class FakeMinio:
    def __init__(self, fail_times=0, want_bucket="b"):
        self.fail_times = fail_times
        self.calls = 0
        self.want_bucket = want_bucket
        self.last_headers = None

    class Result:
        def __init__(self, etag="etag123"):
            self.etag = etag

    def put_object(
        self,
        bucket_name,
        object_name,
        data,
        length,
        content_type=None,
        metadata=None,
        headers=None,
    ):
        self.calls += 1
        self.last_headers = headers or {}
        if bucket_name != self.want_bucket:
            raise RuntimeError("No such bucket")
        if self.calls <= self.fail_times:
            raise RuntimeError("transient")
        return FakeMinio.Result(etag="ok-" + str(self.calls))


def test_put_object_retries_and_succeeds():
    fake = FakeMinio(fail_times=2)
    ad = MinioAdapter(fake)
    out = ad.put_object_bytes(
        bucket="b", key="k.txt", data=b"hello", content_type="text/plain"
    )
    assert out["etag"].startswith("ok-")
    # should have retried exactly fail_times + 1
    assert fake.calls == 3
    # md5 header must be present
    assert "Content-MD5" in fake.last_headers


def test_put_object_missing_bucket_maps_error():
    fake = FakeMinio(fail_times=0, want_bucket="other")
    ad = MinioAdapter(fake)
    try:
        ad.put_object_bytes(bucket="b", key="k", data=b"x")
        assert False, "expected error"
    except RuntimeError as e:
        assert "bucket" in str(e).lower()


def test_put_object_accepts_external_md5():
    fake = FakeMinio()
    ad = MinioAdapter(fake)
    out = ad.put_object_bytes(
        bucket="b",
        key="k",
        data=b"abc",
        checksums={"md5": "900150983cd24fb0d6963f7d28e17f72"},
    )
    assert out["key"] == "k"
    # header must be set (adapter base64-encodes the provided hex md5)
    assert "Content-MD5" in fake.last_headers

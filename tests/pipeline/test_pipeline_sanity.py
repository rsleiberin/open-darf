def test_pipeline_imports():
    import apps.pipeline as p  # noqa: F401
    import apps.pipeline.parse as parse
    import apps.pipeline.process as process

    t, hint = parse.extract_text(b"hello", "text/plain")
    assert isinstance(t, str) and isinstance(hint, str)
    rpt = process.run_bias_checks(t)
    assert "cbdt" in rpt and "score" in rpt["cbdt"]

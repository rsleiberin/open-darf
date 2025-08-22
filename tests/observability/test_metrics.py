from apps.observability import metrics


def test_metrics_noop_does_not_throw():
    metrics.increment("ce.decision", {"decision": "ALLOW"})


def test_set_provider_captures():
    class Sink:
        def __init__(self):
            self.calls = []

        def increment(self, name, labels=None):
            self.calls.append((name, dict(labels or {})))

    s = Sink()
    metrics.set_provider(s)
    metrics.increment("foo.bar", {"k": "v"})
    assert s.calls and s.calls[-1][0] == "foo.bar" and s.calls[-1][1]["k"] == "v"

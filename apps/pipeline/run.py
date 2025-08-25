from typing import Iterable, Tuple, Dict, Any
import os
import time
import statistics
from apps.pipeline.parse import extract_text
from apps.pipeline.process import run_bias_checks
from apps.pipeline.receipts import write_receipt


def _percentile(data, p):
    if not data:
        return 0.0
    s = sorted(float(x) for x in data)
    k = (len(s) - 1) * (p / 100.0)
    f, c = int(k), min(int(k) + 1, len(s) - 1)
    if f == c:
        return s[int(k)]
    return s[f] + (s[c] - s[f]) * (k - f)


def _on(key: str) -> bool:
    return str(os.getenv(key, "")).strip().lower() in {"1", "true", "yes", "on"}


def run_once(source, bucket: str = "e2e") -> Tuple[int, str]:
    """
    Pull all refs from `source` (must support .list() & .fetch()),
    parse and process each, and write a receipt.
    If PIPELINE_PERF is truthy, include timing stats & parser counters.
    Returns (count_processed, receipt_path).
    """
    refs: Iterable[str] = list(source.list())
    want_perf = _on("PIPELINE_PERF")
    reports: Dict[str, Any] = {}
    parser_counts: Dict[str, int] = {}
    t_parse, t_process, t_cbdt = [], [], []
    cbdt_runs = 0
    cbdt_findings_total = 0

    for ref in refs:
        b = source.fetch(ref)

        t0 = time.perf_counter()
        text, hint = extract_text(b, "text/plain")
        t1 = time.perf_counter()

        # Optional Anchors pass (flag-gated; lazy import; never-throws)
        anchors_summary = {}
        if _on("PIPELINE_ANCHORS"):
            try:
                from apps.pipeline.anchors import anchors_pass

                ares = anchors_pass(
                    {}, {"doc_id": str(ref), "blocks": [{"id": "b1", "text": text}]}
                )
                anchors_summary = {
                    "algo": ares.algo,
                    "doc_anchor": ares.doc_anchor,
                    "sub_anchors": [
                        {"id": a.id, "start": a.start, "end": a.end}
                        for a in ares.sub_anchors
                    ],
                    "timing_ms": ares.timing_ms,
                }
            except Exception as _e:
                anchors_summary = {"error": type(_e).__name__}

        # Existing bias checks (lightweight stub)
        rpt = run_bias_checks(text)

        # Optional CBDT pass (flag-gated; lazy import; never-throws)
        # Optional Anchors pass (sha256) when PIPELINE_ANCHORS is set
        cbdt_summary: Dict[str, Any] = {}
        if _on("PIPELINE_CBDT"):
            try:
                from apps.pipeline.process.cbdt import (
                    cbdt_pass,
                )  # lazy, keeps PR CI service-free

                t1b = time.perf_counter()
                doc = {
                    "doc_id": str(ref),
                    "blocks": [{"id": "b1", "text": text}],
                    "lang": "en",
                    "mime": "text/plain",
                }
                res = cbdt_pass({}, doc)
                t2b = time.perf_counter()
                if want_perf:
                    t_cbdt.append((t2b - t1b) * 1000.0)
                cbdt_runs += 1
                try:
                    from apps import obs as _obs

                    _obs.increment("runner.cbdt.runs", 1)
                    _obs.increment(
                        "runner.cbdt.findings_total",
                        int(res.summary.get("findings_total", 0)),
                    )
                    _obs.histogram("runner.cbdt.ms", (t2b - t1b) * 1000.0)
                except Exception:
                    pass
                cbdt_findings_total += int(res.summary.get("findings_total", 0))
                cbdt_summary = {
                    "counts_by_label": res.summary.get("counts_by_label", {}),
                    "findings_total": res.summary.get("findings_total", 0),
                    "receipt_path": res.summary.get("receipt_path"),
                    "receipt_last": res.summary.get("receipt_last"),
                    "signals": res.summary.get("signals", []),
                }
            except Exception as e:  # observability must never throw
                cbdt_summary = {"error": type(e).__name__}

        # Optional PROV-O bundle (flag-gated; never throws)
        prov_summary = {}
        if _on("PIPELINE_PROV"):
            try:
                from apps.pipeline.prov import prov_pass

                pres = prov_pass(
                    {}, {"doc_id": str(ref), "blocks": [{"id": "b1", "text": text}]}
                )
                prov_summary = {
                    "jsonld": pres.jsonld,
                    "timing_ms": pres.timing_ms,
                    "receipt_path": pres.receipt_path,
                }
            except Exception as _e:
                prov_summary = {"error": type(_e).__name__}

        # Optional OSCaR pass (flag-gated; never throws)
        oscar_summary = {}
        if _on("PIPELINE_OSCAR"):
            try:
                from apps.pipeline.oscar import oscar_pass

                ores = oscar_pass(
                    {}, {"doc_id": str(ref), "blocks": [{"id": "b1", "text": text}]}
                )
                oscar_summary = {
                    "version": ores.version,
                    "risk_score": ores.risk_score,
                    "tags": ores.tags,
                    "timing_ms": ores.timing_ms,
                    "receipt_path": ores.receipt_path,
                }
            except Exception as _e:
                oscar_summary = {"error": type(_e).__name__}

        t2 = time.perf_counter()

        reports[ref] = {"parser": hint, "bias": rpt}
        if anchors_summary:
            reports[ref]["anchors"] = anchors_summary
        if cbdt_summary:
            reports[ref]["cbdt"] = cbdt_summary
        if prov_summary:
            reports[ref]["prov"] = prov_summary
        if oscar_summary:
            reports[ref]["oscar"] = oscar_summary
        if prov_summary:
            reports[ref]["prov"] = prov_summary

        parser_counts[hint] = parser_counts.get(hint, 0) + 1
        if want_perf:
            t_parse.append((t1 - t0) * 1000.0)
            t_process.append((t2 - t1) * 1000.0)

    payload: Dict[str, Any] = {"count": len(refs), "reports": reports}
    if want_perf:
        payload["perf"] = {
            "parse_ms": {
                "p50": _percentile(t_parse, 50),
                "p95": _percentile(t_parse, 95),
                "max": max(t_parse) if t_parse else 0.0,
                "avg": statistics.fmean(t_parse) if t_parse else 0.0,
                "n": len(t_parse),
            },
            "process_ms": {
                "p50": _percentile(t_process, 50),
                "p95": _percentile(t_process, 95),
                "max": max(t_process) if t_process else 0.0,
                "avg": statistics.fmean(t_process) if t_process else 0.0,
                "n": len(t_process),
            },
        }
        if t_cbdt:
            payload["perf"]["cbdt_ms"] = {
                "p50": _percentile(t_cbdt, 50),
                "p95": _percentile(t_cbdt, 95),
                "max": max(t_cbdt) if t_cbdt else 0.0,
                "avg": statistics.fmean(t_cbdt) if t_cbdt else 0.0,
                "n": len(t_cbdt),
            }
        payload["obs"] = {
            "parser_counts": parser_counts,
            "cbdt_runs": cbdt_runs,
            "cbdt_findings_total": cbdt_findings_total,
        }

    path = write_receipt(bucket, "run_once", payload)
    return len(refs), path

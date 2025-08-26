# Phase 5 — ML Integration (Week 1: SciBERT interface)

Status: Stub extractor added (service-free).
Enable: EXTRACTOR_SCI=1
Contracts: apps/extractors/scibert.py → extract(text) -> list[Entity] with Entity {text,label,start,end}

Local usage (example):

    export EXTRACTOR_SCI=1
    python - <<'PY'
    from apps.extractors import scibert
    text = "TP53 and BRCA1 with doi:10.1000/xyz123; NaCl 5 mg; PMID: 12345678."
    for e in scibert.extract(text):
        print(e)
    PY

Tests:

- Golden: tests/extractors/test_scibert_stub.py
- Perf (opt-in): RUN_PERF=1 pytest -q tests/performance/test_scibert_perf.py

## Week 2 — BioBERT interface

**Enable:** EXTRACTOR_BIO=1
Module: apps/extractors/biobert.py  →  extract(text) -> list[Entity]

## Week 2 — BioBERT interface

**Enable:** EXTRACTOR_BIO=1
Module: apps/extractors/biobert.py  →  extract(text) -> list[Entity]

## Week 3 — Text2NKG interface

**Enable:** EXTRACTOR_NKG=1
Module: apps/extractors/text2nkg.py → extract(text) -> list[Hyperedge]
Perf: RUN_PERF=1 pytest -q tests/performance/test_text2nkg_perf.py

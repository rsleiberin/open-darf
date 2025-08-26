from __future__ import annotations

import os
import re
from dataclasses import dataclass
from typing import Iterable, List, Optional, Tuple

ENABLE_ENV = "EXTRACTOR_BIO"


@dataclass(frozen=True)
class Entity:
    text: str
    label: str
    start: int
    end: int


# Mini vocab for CI-safe stub
_GENES = {"TP53", "EGFR", "BRCA1"}
_DISEASES = {"cancer", "glioblastoma", "influenza"}
_DRUGS = {"aspirin", "ibuprofen", "cisplatin"}
_PMID_RE = re.compile(r"\bPMID:\s?\d+\b", re.IGNORECASE)


def is_enabled(env: Optional[dict] = None) -> bool:
    e = env if env is not None else os.environ
    return str(e.get(ENABLE_ENV, "")).strip().lower() in {"1", "true", "yes", "on"}


def _iter_vocab(text: str, label: str, vocab: set[str]) -> Iterable[Entity]:
    for tok in vocab:
        for m in re.finditer(rf"\b{re.escape(tok)}\b", text, flags=re.IGNORECASE):
            yield Entity(text=m.group(0), label=label, start=m.start(), end=m.end())


def _iter_pmid(text: str) -> Iterable[Entity]:
    for m in _PMID_RE.finditer(text):
        yield Entity(text=m.group(0), label="PMID", start=m.start(), end=m.end())


# --- Disambiguation helpers ---
def candidate_labels_for(token: str) -> Tuple[bool, bool]:
    t = token.upper()
    return (t in _GENES, token.lower() in _DISEASES)


def disambiguate(token: str) -> str:
    """Return preferred label for an ambiguous token."""
    is_gene, is_disease = candidate_labels_for(token)
    if is_gene and is_disease:
        return "GENE_SYMBOL"  # prefer gene over disease in tie
    if is_gene:
        return "GENE_SYMBOL"
    if is_disease:
        return "DISEASE"
    return "UNKNOWN"


def extract(text: str) -> List[Entity]:
    if not is_enabled():
        raise RuntimeError("BioBERT extractor disabled — set EXTRACTOR_BIO=1")
    if not text:
        return []

    ents: List[Entity] = []
    ents.extend(list(_iter_pmid(text)))
    ents.extend(list(_iter_vocab(text, "DRUG", _DRUGS)))

    # For tokens that might be gene or disease, emit single disambiguated label
    for tok in sorted(_GENES | _DISEASES, key=len, reverse=True):
        for m in re.finditer(rf"\b{re.escape(tok)}\b", text, flags=re.IGNORECASE):
            label = disambiguate(m.group(0))
            if label != "UNKNOWN":
                ents.append(
                    Entity(text=m.group(0), label=label, start=m.start(), end=m.end())
                )

    ents.sort(key=lambda e: (e.start, e.end, e.label))
    try:
        from apps.audit import receipts  # type: ignore

        receipts.make_jsonl_sink("extractors")(
            {"component": "biobert_stub", "event": "extract", "count": len(ents)}
        )
    except Exception:
        pass
    return ents

from __future__ import annotations
import os
from typing import Any, Dict, List
from dataclasses import dataclass
from apps.guards import constitutional as constitutional_guard


@dataclass
class BioEntity:
    text: str
    label: str
    start: int
    end: int
    score: float
    guard_decision: str
    reason_code: str
    provenance: Dict[str, Any]


class BioBERTExtractor:
    """
    Biomedical NER via transformers pipeline when enabled.
    - Gate: EXTRACTOR_BIO=1
    - Model: BIO_MODEL_NAME (default a biomedical NER); Task: BIO_TASK (default 'token-classification'/'ner')
    - Safe fallbacks if deps or model are missing.
    """

    def __init__(self) -> None:
        self.enabled = os.getenv("EXTRACTOR_BIO", "0") == "1"
        # Default to a biomedical NER checkpoint; user can override.
        self.model_name = os.getenv("BIO_MODEL_NAME", "d4data/biomedical-ner-all")
        self.task = os.getenv("BIO_TASK", os.getenv("SCI_TASK", "ner"))
        self._pipe = None
        self._init_error = None
        if self.enabled:
            try:
                from transformers import pipeline  # type: ignore

                # grouped_entities helps consolidate B- / I- sequences when available
                self._pipe = pipeline(
                    self.task, model=self.model_name, grouped_entities=True
                )
            except Exception as e:
                self._init_error = str(e)
                self._pipe = None

    def is_enabled(self) -> bool:
        return self.enabled

    def health(self) -> Dict[str, Any]:
        return {
            "enabled": self.enabled,
            "model_name": self.model_name,
            "task": self.task,
            "pipe_ready": self._pipe is not None,
            "init_error": self._init_error,
        }

    def extract(self, text: str) -> Dict[str, Any]:
        # Pre-guard: empty/invalid text is DENY
        guard = constitutional_guard.evaluate({"text": text})
        if guard.decision == "DENY":
            return {
                "decision": "DENY",
                "reason_code": guard.reason_code,
                "entities": [],
                "provenance": {"stage": "pre_guard"},
            }

        # Disabled path: safe stub
        if not self.enabled:
            return {
                "decision": guard.decision,
                "reason_code": "disabled",
                "entities": [],
                "provenance": {"enabled": False, "stage": "disabled_stub"},
            }

        # Model not ready: INDETERMINATE to avoid false positives
        if self._pipe is None:
            final = constitutional_guard.precedence(guard.decision, "INDETERMINATE")
            return {
                "decision": final,
                "reason_code": "model_unavailable",
                "entities": [],
                "provenance": {
                    "enabled": True,
                    "stage": "model_unavailable",
                    "error": self._init_error,
                },
            }

        # Inference
        raw = self._pipe(text)  # type: ignore[call-arg]
        ents: List[BioEntity] = []
        final = guard.decision
        for r in raw:
            ent_text = r.get("word") or r.get("entity_group") or ""
            start = int(r.get("start", -1))
            end = int(r.get("end", -1))
            label = r.get("entity_group") or r.get("entity") or "ENTITY"
            score = float(r.get("score", 0.0))
            eg = constitutional_guard.evaluate({"text": ent_text})
            final = constitutional_guard.precedence(final, eg.decision)
            ents.append(
                BioEntity(
                    text=ent_text,
                    label=str(label),
                    start=start,
                    end=end,
                    score=score,
                    guard_decision=eg.decision,
                    reason_code=eg.reason_code,
                    provenance={"model": self.model_name},
                )
            )
        return {
            "decision": final,
            "reason_code": "ok",
            "entities": [e.__dict__ for e in ents],
            "provenance": {
                "enabled": True,
                "stage": "inference",
                "model": self.model_name,
            },
        }

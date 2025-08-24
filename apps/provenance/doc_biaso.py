# SPDX-License-Identifier: MIT
from __future__ import annotations
from dataclasses import dataclass
from typing import Dict

# Minimal ontology shim for classification + version tagging
_DBO_IRI: Dict[str, str] = {
    "citation_bias": "doc-biaso:CitationBias",
    "gender_bias": "doc-biaso:GenderBias",
    "methodology_bias": "doc-biaso:MethodologyBias",
    "representation_bias": "doc-biaso:RepresentationBias",
    "outcome_bias": "doc-biaso:OutcomeBias",
}


@dataclass(frozen=True)
class DocBiasOntology:
    version: str = "0.1.0"

    def classify_bias_type(self, key: str) -> str:
        return _DBO_IRI.get(key, "doc-biaso:UnknownBias")


def load_doc_biaso_ontology() -> DocBiasOntology:
    return DocBiasOntology()

from __future__ import annotations
from typing import Any, Dict, List
import os
from apps.guards import constitutional as CG
from apps.guards.middleware import guarded_infer
from apps.extractors.scibert_extractor import SciBERTExtractor
from apps.extractors.biobert_extractor import BioBERTExtractor
from apps.extractors.text2nkg_extractor import Text2NKGExtractor
from apps.knowledge_graph.temporal_model import TemporalModel


def _prec_merge(a: str, b: str) -> str:
    return CG.precedence(a, b)


def extract_all(text: str) -> Dict[str, Any]:
    envs_entities: List[Dict[str, Any]] = []
    envs_relations: List[Dict[str, Any]] = []
    envs_temporal: List[Dict[str, Any]] = []

    if os.getenv("EXTRACTOR_SCI", "0") == "1":
        envs_entities.append(guarded_infer(text, SciBERTExtractor().extract, "sci"))
    if os.getenv("EXTRACTOR_BIO", "0") == "1":
        envs_entities.append(guarded_infer(text, BioBERTExtractor().extract, "bio"))
    if os.getenv("EXTRACTOR_TEXT2NKG", "0") == "1":
        envs_relations.append(
            guarded_infer(text, Text2NKGExtractor().extract, "text2nkg")
        )
    if os.getenv("TEMPORAL_GRAPH_MODEL", "0") == "1":
        envs_temporal.append(guarded_infer(text, TemporalModel().infer, "temporal"))

    if not (envs_entities or envs_relations or envs_temporal):
        return {
            "decision": "INDETERMINATE",
            "reason_code": "no_extractors_enabled",
            "entities": [],
            "relations": [],
            "temporals": [],
            "provenance": {"orchestrator": "entity_extraction"},
        }

    final_decision = "ALLOW"
    entities: List[Dict[str, Any]] = []
    relations: List[Dict[str, Any]] = []
    temporals: List[Dict[str, Any]] = []

    for env in envs_entities:
        final_decision = _prec_merge(
            final_decision, env.get("decision", "INDETERMINATE")
        )
        entities.extend(env.get("entities", []))
    for env in envs_relations:
        final_decision = _prec_merge(
            final_decision, env.get("decision", "INDETERMINATE")
        )
        relations.extend(env.get("relations", []))
    for env in envs_temporal:
        final_decision = _prec_merge(
            final_decision, env.get("decision", "INDETERMINATE")
        )
        temporals.extend(env.get("events", env.get("temporals", [])))

    out = {
        "decision": final_decision,
        "reason_code": "ok",
        "entities": entities,
        "relations": relations,
        "temporals": temporals,
        "provenance": {"orchestrator": "entity_extraction", "middleware": True},
    }
    return out

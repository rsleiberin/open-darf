from dataclasses import dataclass
from datetime import datetime


@dataclass
class IngestionEvent:
    entity_id: str
    activity_id: str
    agent_id: str
    ts_iso: str


def cypher_for_ingestion(e: IngestionEvent) -> str:
    """
    Pure function producing PROV-O-compliant Cypher for ingestion provenance.
    IO/driver calls are intentionally out-of-scope for unit tests.
    """
    return f"""
    MERGE (doc:Entity:Document {{id: '{e.entity_id}', type: 'Document'}})
    MERGE (act:Activity {{id: '{e.activity_id}', type: 'DocumentIngestion', startTime: '{e.ts_iso}'}})
    MERGE (ag:Agent {{id: '{e.agent_id}', type: 'IngestionService'}})
    MERGE (doc)-[:wasGeneratedBy]->(act)
    MERGE (act)-[:wasAssociatedWith]->(ag)
    """


def build_ingestion_event(entity_id: str, agent_id: str) -> IngestionEvent:
    return IngestionEvent(
        entity_id=entity_id,
        activity_id=f"ingest_{entity_id}",
        agent_id=agent_id,
        ts_iso=datetime.utcnow().isoformat(),
    )

/* Phase 7F — Neo4j composite indexes & constraints (dry-run plan) */
CREATE CONSTRAINT IF NOT EXISTS unique_document_id
FOR (d:Document) REQUIRE d.id IS UNIQUE;
CREATE CONSTRAINT IF NOT EXISTS node_precedent_id
FOR (p:Precedent) REQUIRE p.id IS UNIQUE;
CREATE INDEX IF NOT EXISTS idx_doc_anchor_composite
FOR (a:Anchor) ON (a.doc_id, a.span_start, a.span_end);
CREATE INDEX IF NOT EXISTS idx_relation_key
FOR (r:Relation) ON (r.type, r.source_id, r.target_id);
CREATE INDEX IF NOT EXISTS idx_vote_decision
FOR (v:OperatorVote) ON (v.decision, v.timestamp);
CREATE INDEX IF NOT EXISTS idx_constraint_key
FOR (c:Constraint) ON (c.key, c.version);

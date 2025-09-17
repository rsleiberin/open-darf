#!/usr/bin/env bash
set -euo pipefail

: "${POSTGRES_USER:=postgres}"
: "${POSTGRES_PASSWORD:?POSTGRES_PASSWORD required}"
: "${POSTGRES_DB:=postgres}"
: "${POSTGRES_HOST:=localhost}"
: "${POSTGRES_PORT:=5432}"

PGURL="postgresql://${POSTGRES_USER}:${POSTGRES_PASSWORD}@${POSTGRES_HOST}:${POSTGRES_PORT}/${POSTGRES_DB}"

# Build decision via Neo4j (placeholder timings); real rule eval is wired upstream.
DECISION="INDETERMINATE"
REASON="no_applicable_rule"
NEO4J_MS="${NEO4J_MS_OVERRIDE:-2000}"

# Insert receipt using psql-only JSON construction to avoid quoting bugs.
psql "$PGURL" -v ON_ERROR_STOP=1 <<'PSQL'
DO $$
DECLARE v_id BIGINT;
BEGIN
  INSERT INTO audit.receipts(component, action, status, details, duration_ms)
  VALUES (
    'constitutional_engine',
    'rule_eval_write_evidence_bundle',
    'INDETERMINATE',
    jsonb_build_object(
      'context', jsonb_build_object(
        'actor','pipeline',
        'action','write_evidence_bundle',
        'irreversible', true,
        'has_review', false
      ),
      'rule_priority','DENY_PRECEDENCE',
      'rule_id','R0',
      'neo4j_ms', 2000
    ),
    2000
  )
  RETURNING id INTO v_id;
END $$;
PSQL

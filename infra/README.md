# Open-DARF Infrastructure

This directory contains database initialization scripts for the constitutional validation infrastructure.

## Database Systems

### Neo4j - Knowledge Graph

Purpose: Store constitutional constraints, relationships, and governance structures

Initialization: neo4j/init/001-constitutional-schema.cypher

Schema Components:
- Constitutional node types (rules, constraints, policies)
- Relationship types (enforces, delegates, overrides)
- Sovereignty and authorization hierarchies

### PostgreSQL - Audit Trail

Purpose: Store W3C PROV-O compliant provenance and audit records

Initialization: postgres/init/001-audit-schema.sql

Schema Components:
- Activity logging (who did what when)
- Entity provenance (data origin tracking)
- Agent attribution (responsibility chains)

## Usage

These scripts are automatically executed when Docker containers start via docker-compose.yml.

No manual execution required for standard deployment.

## Customization

To add custom schemas or extensions:

1. Create new numbered file (e.g., 002-custom-schema.sql)
2. Place in appropriate init/ directory
3. Restart containers: docker compose down && docker compose up -d

Scripts execute in alphanumeric order.

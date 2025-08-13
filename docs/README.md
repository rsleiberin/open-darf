# Documentation Structure

## Core Decision Documentation
- `decisions/` - ADR repository (25 ADRs, authoritative source)
- `templates/` - ADR templates for decision documentation

## Production System Documentation  
- `api/` - REST API documentation (generated from code)
- `architecture/` - System architecture docs (generated from ADRs)
- `deployment/` - Production deployment and operations guides

## Reference Materials
- `reference/` - Source research documents (PDFs)
- `process/` - Development and contribution processes

## Legacy (To be replaced)
- `automation/ingestion_output/` - Manual tracking files (will be replaced by database)

The ADRs in `decisions/` contain the authoritative technical decisions.
All other documentation should derive from or support those decisions.

## Maintenance
- Reference dedupe report: [docs/reference/_dedupe_report.md](reference/_dedupe_report.md)

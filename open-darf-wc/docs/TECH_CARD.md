# Tech Card — Open-DARF

## Topology
- Local Docker Compose stack
- Graph database service
- Object storage or filesystem evidence sink
- Scripted health checks and validation routines

## Configuration
- All secrets via environment variables in `.env`
- Compose references variables only (no inline credentials)
- Example placeholders live in `.env.sample`

## Operational Scripts
- `install.*` and `install_and_run.*` — bootstrap flows
- `run.*` — bring services up in the right order
- `health_wait.*` — wait for service readiness
- `validate.*` and `validator_acceptance.*` — smoke and acceptance checks

## Security Notes
- No hardcoded credentials in scripts
- Ignore lists prevent committing local artifacts and audit previews
- Infra seed content may be vendor-managed and excluded from public syncs

## Maintenance
- Keep Docker images updated
- Periodically rotate credentials in `.env`
- Re-run validation after dependency upgrades

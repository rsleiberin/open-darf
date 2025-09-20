# User Card — Open-DARF

## Who This Is For
Operators who want a clean local environment to validate data/graph workflows with security-conscious defaults.

## Prerequisites
- Docker and Docker Compose
- Bash (Linux/macOS) or PowerShell (Windows)
- Ability to set environment variables in a local `.env` file

## Install (Linux)
1. Review `.env.sample`, then create `.env` with your values.
2. Run `./start.sh`.
3. Verify services with `./scripts/health_wait.sh`.

## Install (Windows PowerShell)
1. Review `.env.sample`, then create `.env` with your values.
2. Run `./START.ps1`.
3. Verify services with `./scripts/health_wait.ps1`.

## Common Tasks
- Start services: run script for your platform.
- Validate suite: `./scripts/validate.sh` or `./scripts/validate.ps1`.
- Stop services: `./scripts/kill_switch.sh` or `./scripts/kill_switch.ps1`.

## Support
If something fails to start, check Docker logs and ensure all required environment variables in `.env` are set.

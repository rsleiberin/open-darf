# Open-DARF — Peer Validator

Open-DARF provides a reproducible peer-validation environment for local evaluation of data pipelines and lightweight graph services. The working copy is designed for clean installation on fresh Windows and Linux hosts, with security-conscious defaults and environment-based configuration.

## Goals

- Clear first-run experience on Windows and Linux
- Security-first configuration (no embedded secrets)
- Minimal local footprint; compose services start fast
- Professional documentation suitable for academic and enterprise contexts

## What’s Included

- Linux and Windows entrypoints (start.sh, START.ps1)
- Docker Compose services for a local graph database and evidence store
- Scripts for install, run, validation, and health checks
- User and technical cards in the `docs/` directory

## Quick Start (Linux)

1. Copy `.env.sample` to `.env` and set values.
2. Run `./start.sh` to initialize local services.
3. Run `./scripts/validate.sh` to exercise the validator suite.

Note: do not commit `.env`. The project references secrets via environment variables only.

## Quick Start (Windows PowerShell)

1. Copy `.env.sample` to `.env` and set values.
2. Run `./START.ps1`.
3. Run `./scripts/validate.ps1` to exercise the validator suite.

## Configuration

All credentials and endpoints are provided via environment variables. The Compose file references variables only. Example keys are present in `.env.sample` as placeholders.

## Documentation

- `docs/USER_CARD.md` — operator-focused guide for local use
- `docs/TECH_CARD.md` — technical overview and service map
- `docs/learning/` — background materials and walkthroughs

## Security Posture

- No hardcoded credentials in scripts or Compose
- Example environment values use neutral placeholders
- Generated artifacts and audit previews are excluded from version control

## License

See LICENSE file if provided by the repository owner. If absent, usage is limited to evaluation on local hosts as provided.

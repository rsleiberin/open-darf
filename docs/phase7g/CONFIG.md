# Phase 7G — Config Surface (Pydantic + Compose Profiles)

**Scope:** Canonical config surface via Pydantic `BaseSettings` with prefixes `DB_`, `API_`, `LLM_`.  
**Artifacts:**
- `packages/darf_config/settings.py` — runtime config
- `configs/.env.sample` → copy to `.env.local` for dev
- `scripts/config_validate.py` — validation CLI (warns if `pydantic` missing)
- `compose/compose.yaml` — profiles: `dev`, `staging`, `prod` (no secrets committed)

**Secrets Policy:** Use Docker/Podman secrets or Vault—not repo files. The compose file includes commented examples.  
**Next:** CI job to import `packages.darf_config` and validate across profiles.


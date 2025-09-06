# Phase 7F — Revocation Planner (read-only)

Computes cascade scope for revocations on a directed dependency graph (A→B meaning B depends on A).
Outputs a plan JSON; no external datastore mutations are performed.

## Usage
scripts/phase7f/revocation_planner.py --edges path/to/edges.json --start path/to/starts.json

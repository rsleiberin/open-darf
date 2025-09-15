# Phase 7T Implementation Handoff: Enhanced Validation with Provenance Anchoring
(Handoff digest recorded from session context.)
- Grant deadline: 2025-10-01
- Scope: Add SHA-256 content anchoring, deterministic JSON manifest, minimal provenance receipts, MinIO CAS, exact-byte hashing for binaries, light text canonicalization (UTF-8, LF, trim trailing spaces).
- Back-compat: Preserve 7S evidence and CLI surfaces; enhanced package is additive.
- Acceptance: Anchors for all artifacts, manifest stability across hosts, self-verify script, no perf regression, dedup metrics.

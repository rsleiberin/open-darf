# Migration: Phase 7S → Phase 7T (Additive)

What changes: Phase 7T adds provenance (cryptographic manifests, receipts, CAS) next to your current 7S evidence. No 7S commands are removed or altered.

Keep using 7S:
- finalize-phase7s
- acceptance-phase7s
- review-packet

New, optional targets:
- verify-provenance
- qa-provenance
- help-provenance

Outputs:
- Deterministic manifest with self-hash
- Local CAS at .cas/sha256
- Audited receipts under docs/audit/phase7t
- Optional enhanced bundle *_prov.tar.gz alongside your legacy bundle

Rollback:
- Simply ignore the new files/targets; 7S surfaces remain intact.

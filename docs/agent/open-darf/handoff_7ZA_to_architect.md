# Handoff — Phase 7ZA → Architect — Open-DARF Working Copy

Date (UTC): 20250919T022939Z

## Scope
- All operations limited to `open-darf-wc/` subtree.

## Completed
- Inventory, classification, and receipts.
- Scoped signals scan + redaction map.
- Header previews applied for 31 candidates; zero preview misses.
- Dual-audience docs: USER_CARD.md and TECH_CARD.md.
- Local CI guards (doc fences, header presence).
- PR plan for header insertion (preview-only).

## Pending (Requires Approval)
- **Doc fence normalization** across public docs (will modify files).
- (Optional) Apply headers to real files using preview mirror.

## Decision Gate (Tri-State)
- **ALLOW**: Approve applying headers + doc fence normalization in `open-darf-wc/`.
- **DENY**: Defer changes; keep repo private.
- **INDETERMINATE**: Request modifications / further evidence.

## Receipts Index
- Readiness: open-darf-wc/docs/audit/phase7za/20250919T022939Z/readiness_report.md
- Apply list: open-darf-wc/docs/audit/phase7za/20250919T021006Z/header_apply_list.tsv
- Preview check: open-darf-wc/docs/audit/phase7za/20250919T021006Z/preview_header_check.tsv
- Coverage: open-darf-wc/docs/audit/phase7za/20250919T020732Z/comment_coverage.json
- Redaction map: open-darf-wc/docs/audit/phase7za/20250919T020732Z/redaction_map.tsv
- Preview root: open-darf-wc/_header_applied_preview

## Public Flip Protocol (Only on Architect ALLOW)
1) Apply headers via `tools/apply_headers.sh`.
2) Normalize fences; ensure guards pass.
3) Commit/PR with receipts references; request Architect sign-off.
4) After merge, Architect flips visibility (you required formal permission).

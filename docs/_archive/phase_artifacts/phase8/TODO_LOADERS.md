# TODO — Dataset-Aware Loaders

## BioRED (official/norm)
- [ ] Preserve relation annotations through dedup recount
- [ ] Include stable IDs in hash: PMID + section + paragraph offsets
- [ ] Regression test: zero relations MUST NOT appear after dedup snapshot

## SciERC (json/norm)
- [ ] Split-aware loader (train/dev/test) with consistent doc_id mapping
- [ ] Validate entity/relation counts after dedup (±1% tolerance)

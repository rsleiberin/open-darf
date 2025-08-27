# Handoff — Phase 4 Kickoff

**State:** Labels/templates enforced; migration complete; perf gate in place.
**Open Items:** Roadmap execution + benchmarks (opt-in), manual branch protection check.
**Planning Issues:** #304 SciBERT, #305 BioBERT, #306 Text2NKG, #307 Graph-State LSTM.

**Runbooks:**
- Label hygiene: var/infodump/*/label_apply_next.sh (PREVIEW=1 / APPLY=1)
- Phase migration: var/infodump/*/phase_migrate.sh
- Snapshots live: gh issue list … > var/infodump/<stamp>/

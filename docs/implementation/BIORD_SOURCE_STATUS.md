# BioRED Source Status (Phase 6C)

The automated fetch in `scripts/datasets_fetch.py --task biored` currently fails because all configured source URLs return 404.
Until mirrors are updated, use **manual mode**:

- Place normalized splits at:
  - `data/biored_norm/train.jsonl`
  - `data/biored_norm/dev.jsonl`
  - `data/biored_norm/test.jsonl`

**Important:** BioBERT is a *cased* model. Do **not** lowercase the text during normalization, or you will depress recall/F1.

This file exists to make CI reviewers aware of the situation in the PR.

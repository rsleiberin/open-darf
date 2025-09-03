SciERC char-offset gold (by-sentence)
====================================

Provide char-offset JSONL files:

- var/datasets/normalized/scierc/dev.jsonl
- var/datasets/normalized/scierc/test.jsonl

Each record may be either:
1) {"text":"...","spans":[{"start":S,"end":E,"label":"TYPE"}, ...]}
2) {"sentences":[{"text":"...","spans":[...]}, ...]}

Alternatively set:
export GOLD_FORCE_DIR_SCIERC=/abs/path/with/dev_and_test_jsonl

Then run:
bash OP_SCIERC_RUN_SAFE

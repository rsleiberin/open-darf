# Phase 6C Benchmark Results
Generated: 2025-08-30 21:06:46Z

## SciERC
**SciERC**

- Entity micro-F1: **0.0000**
- Relation micro-F1: **0.0000**
- Target(s): {'entity_f1': 0.67}
- Pass: **False**

## BioRED
**BioRED**

- Entity micro-F1: **0.0000**
- Relation micro-F1: **0.0000**
- Target(s): {'entity_f1': 0.9, 'relation_f1': 0.65}
- Pass: **False**


## BioRED — biomedical NER (approximate, dev)
**Model:** d4data/biomedical-ner-all
**Eval:** string-match (dev, 64 docs)

- Precision: **0.0681**
- Recall: **0.1491**
- Entity micro-F1: **0.0935**
- Docs scored: 64

_Generated: 2025-08-30 22:14:03Z_


## BioRED — biomedical NER (approximate, test)
**Model:** d4data/biomedical-ner-all
**Eval:** string-match (test, 100 docs)

- Precision: **0.0904**
- Recall: **0.1945**
- Entity micro-F1: **0.1235**
- Docs scored: 100

_Generated: 2025-08-30 22:25:32Z_


## SciERC — dictionary-match baseline (test)
**Model:** dictionary from train (string-match)
**Eval:** term overlap (test)

- Precision: **0.0213**
- Recall: **0.1054**
- Entity micro-F1: **0.0355**
- Docs scored: 100

_Generated: 2025-08-30 22:29:39Z_


## SciERC — official-style entity metric (test)
**Predictor:** train-derived dictionary (greedy longest-match)
**Metric:** exact span+label micro-F1 (test)

- Precision: **0.1104**
- Recall: **0.0901**
- Entity micro-F1: **0.0992**
- Gold spans: 1685 · Pred spans: 5479

_Generated: 2025-08-30 22:34:08Z_

## BioRED — NER (trained BioBERT, test)

- Token micro-F1: **0.0000**
- Entity micro-F1 (span+label): **0.6310**
- Train runtime: 13.22s

_Generated: 2025-08-30 22:58:51Z_

(Updated) BioRED token micro-F1: **0.0000** _at 2025-08-30 23:03:10Z_


## Handoff snapshot (2025-08-30 23:10:05Z)
**SciERC** entity micro-F1: **0.3070**  |  **BioRED** entity micro-F1: **0.6310**
(Validator schema present: `scierc_scores_ml_test.json`, `biored_scores_ml_test.json`; see `var/reports/phase6c/gates.json`.)

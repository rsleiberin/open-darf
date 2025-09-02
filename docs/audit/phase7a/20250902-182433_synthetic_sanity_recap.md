# Phase-7A — Synthetic Sanity Recap

**Scope:** This document captures *sanity-only* scoring using synthetic sentence-level gold derived from our own NKG nodes (BioRED & SciERC). These numbers are not benchmarks.

## Sanity Scoreboard (latest)
| Dataset/Split | P | R | F1 | TP | FP | FN | Gold SIDs | Gold Path |
|---|---:|---:|---:|---:|---:|---:|---:|---|
| scierc/dev | 1.000 | 1.000 | 1.000 | 3 | 0 | 0 | 1 | `var/datasets/text/scierc_gold_synth/dev.jsonl` |
| scierc/test | 1.000 | 1.000 | 1.000 | 3 | 0 | 0 | 1 | `var/datasets/text/scierc_gold_synth/test.jsonl` |

## Constitutional Overhead Gate
- Threshold (p95): **< 1000.0 μs**
- Gate pass: **True**
  - `var/receipts/phase7a/text2nkg/biored_dev_20250902-163549/audit_summary.json` → p50=0.100μs, p95=0.160μs, p99=0.210μs (calls=1149)
  - `var/receipts/phase7a/text2nkg/biored_dev_20250902-165508/audit_summary.json` → p50=0.070μs, p95=0.131μs, p99=0.200μs (calls=1149)
  - `var/receipts/phase7a/text2nkg/biored_dev_20250902-170653/audit_summary.json` → p50=0.070μs, p95=0.100μs, p99=0.131μs (calls=1149)
  - `var/receipts/phase7a/text2nkg/biored_dev_20250902-174018/audit_summary.json` → p50=1.493μs, p95=1.493μs, p99=1.493μs (calls=1)
  - `var/receipts/phase7a/text2nkg/biored_dev_20250902-180359/audit_summary.json` → p50=0.070μs, p95=0.100μs, p99=0.141μs (calls=1149)
  - `var/receipts/phase7a/text2nkg/biored_dev_20250902-180837/audit_summary.json` → p50=0.070μs, p95=0.120μs, p99=0.150μs (calls=1149)
  - `var/receipts/phase7a/text2nkg/biored_test_20250902-163552/audit_summary.json` → p50=0.070μs, p95=0.100μs, p99=0.120μs (calls=1108)
  - `var/receipts/phase7a/text2nkg/biored_test_20250902-165511/audit_summary.json` → p50=0.070μs, p95=0.110μs, p99=0.150μs (calls=1108)
  - `var/receipts/phase7a/text2nkg/biored_test_20250902-170710/audit_summary.json` → p50=0.070μs, p95=0.121μs, p99=0.200μs (calls=1108)
  - `var/receipts/phase7a/text2nkg/biored_test_20250902-174022/audit_summary.json` → p50=1.653μs, p95=1.653μs, p99=1.653μs (calls=1)
  - `var/receipts/phase7a/text2nkg/biored_test_20250902-180400/audit_summary.json` → p50=0.080μs, p95=0.120μs, p99=0.150μs (calls=1108)
  - `var/receipts/phase7a/text2nkg/biored_test_20250902-180837/audit_summary.json` → p50=0.070μs, p95=0.090μs, p99=0.121μs (calls=1108)
  - `var/receipts/phase7a/text2nkg/scierc_dev_20250902-170714/audit_summary.json` → p50=2.215μs, p95=2.215μs, p99=2.215μs (calls=1)
  - `var/receipts/phase7a/text2nkg/scierc_test_20250902-170718/audit_summary.json` → p50=2.726μs, p95=2.726μs, p99=2.726μs (calls=1)

> Next: Replace synthetic gold with true sentence-level BioRED/SciERC gold to unlock benchmark reproduction (Group 1.2).
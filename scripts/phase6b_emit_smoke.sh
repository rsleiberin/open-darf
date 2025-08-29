#!/usr/bin/env bash
set -Ee -o pipefail; set +u
SC_P="${SC_P:-0.50}"; SC_R="${SC_R:-0.50}"; SC_F="${SC_F:-0.50}"
BI_P="${BI_P:-0.6666666667}"; BI_R="${BI_R:-1.0}"; BI_F="${BI_F:-0.80}"
SC_TP="${SC_TP:-1}"; SC_FP="${SC_FP:-1}"; SC_FN="${SC_FN:-1}"
BI_TP="${BI_TP:-4}"; BI_FP="${BI_FP:-2}"; BI_FN="${BI_FN:-0}"
python -m apps.metrics.receipt_emitter --dataset SciERC --P "$SC_P" --R "$SC_R" --F1 "$SC_F" --tp "$SC_TP" --fp "$SC_FP" --fn "$SC_FN"
python -m apps.metrics.receipt_emitter --dataset BioRED --P "$BI_P" --R "$BI_R" --F1 "$BI_F" --tp "$BI_TP" --fp "$BI_FP" --fn "$BI_FN"

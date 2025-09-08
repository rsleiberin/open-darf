# SciERC Relation Data Contract

- Parser receipt: `var/receipts/phase7g/re_error_analysis/20250908-044925_syntaxfix`
- Shapes summary: `var/receipts/phase7g/re_error_analysis/20250908-044925_syntaxfix/shapes.json`

Observed: relations are nested lists of items [h_s, h_e, t_s, t_e, 'REL']; entities under `ner` are nested lists of triples [s, e, type] (token spans).
Spans are token-indexed; source end is inclusive and converted to exclusive for alignment.

## Example Normalized Relation


---
_Appended at 20250908-051135 (receipt: var/receipts/phase7g/re_error_analysis/20250908-051135_docfix)_

## Example Normalized Relation

```json
{"type": "USED-FOR", "head_idx": 0, "tail_idx": 1, "head_span": [4, 5], "tail_span": [6, 18], "shape": "LIST[n=5;NUM+NUM+NUM+NUM+STR]"}
```

# SciERC Relation Shapes & Parser Notes

- Total relation items: **455**
- Resolved to (head,tail): **455**
- Unresolved: **0**

## Top Shapes
- `LIST[n=5;NUM+NUM+NUM+NUM+STR]` → 455

## Top Relation Type × (HeadEnt, TailEnt)
- `USED-FOR` : Method → Task — 36
- `USED-FOR` : Generic → Task — 23
- `USED-FOR` : Method → Method — 23
- `USED-FOR` : Method → OtherScientificTerm — 22
- `USED-FOR` : Method → Generic — 17
- `CONJUNCTION` : OtherScientificTerm → OtherScientificTerm — 17
- `CONJUNCTION` : Method → Method — 15
- `USED-FOR` : Generic → OtherScientificTerm — 13
- `HYPONYM-OF` : OtherScientificTerm → OtherScientificTerm — 11
- `USED-FOR` : OtherScientificTerm → Method — 10
- `COMPARE` : Generic → Generic — 10
- `USED-FOR` : OtherScientificTerm → OtherScientificTerm — 10
- `CONJUNCTION` : Task → Task — 10
- `USED-FOR` : Generic → Method — 9
- `FEATURE-OF` : OtherScientificTerm → OtherScientificTerm — 9
- `USED-FOR` : Task → Task — 9
- `USED-FOR` : OtherScientificTerm → Task — 9
- `EVALUATE-FOR` : Metric → Method — 8
- `EVALUATE-FOR` : Material → Method — 8
- `HYPONYM-OF` : Method → Method — 7

---
_Appended at 20250908-045752 (receipt: var/receipts/phase7g/re_error_analysis/20250908-045752_post)_

## Relation Distance Insights

- Total normalized relations: **455**
- Token-center distance buckets:
  - 0: 0
  - 1-2: 12
  - 3-5: 180
  - 6-10: 161
  - 11-20: 86
  - 21+: 16
- Directionality: head_before=258, head_after=197, same=0

## Top Relation Labels

- USED-FOR: 214
- CONJUNCTION: 59
- EVALUATE-FOR: 50
- HYPONYM-OF: 44
- FEATURE-OF: 32
- COMPARE: 29
- PART-OF: 27

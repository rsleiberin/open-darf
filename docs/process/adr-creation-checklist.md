# ADR Creation Checklist

## Before Creating an ADR
- [ ] Identify the correct ADR type (CON, VEN, RSH, etc.)
- [ ] Ensure you have the source research/evidence
- [ ] Choose the appropriate template

### Research-First Rule  (2025-08-06)

- [ ] If the work involves a new research document (PDF), create its **RSH** ADR first.  
      Reference that ADR’s ID (e.g. `ADR-YYYY-RSH-NNN`) in every `research_basis` field—do **not** use free-text.
- [ ] Non-RSH ADRs must **not** include `linked_evidence:`; evidence belongs only in the RSH ADR.

## During ADR Creation
- [ ] Copy template content **EXCLUDING the final `---`**
- [ ] Fill in all YAML frontmatter fields
- [ ] Ensure YAML has exactly 2 `---` delimiters (opening and closing)
- [ ] Replace all placeholder text in square brackets `[like this]`

## After ADR Creation
- [ ] `git pull --rebase origin main`  # required
- [ ] Run validation: `./tools/validate-fixed-adrs.sh`
- [ ] Update tracking files: `docs/automation/ingestion_output/doc_manifest.tsv`
- [ ] Commit with descriptive message
- [ ] Verify ADR appears in validation as ✅

## Common Mistakes to Avoid
- ❌ **DO NOT** include the template's final `---` delimiter
- ❌ **DO NOT** leave placeholder text like `[YYMM]` or `[Brief description]`
- ❌ **DO NOT** forget to update tracking files
- ❌ **DO NOT** commit without running validation first

## Quick Validation Command
```bash
# Always run this before committing
./tools/validate-fixed-adrs.sh | grep "$(basename your-new-adr.md)"

```

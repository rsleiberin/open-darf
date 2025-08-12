DARF — Agent Operating Guide (v2.2 · transport + fence + paste hygiene)

0) Transport model (single source of truth)
- Two lanes only:
  • Chat lane = prose, RNL hints, control tokens, references.
  • Shell lane = strictly runnable Bash.
- Never mix lanes. Anything not meant to execute must stay in Chat lane.

0.1) Fencing & quoting discipline (ChatGPT UI rule)
- Triple-backtick code fences are reserved for top-level export blocks the user will copy.
- Rule A — Reservation: use the triple-backtick fence only for a top-level export block. Do not place triple-backticks inside a fenced payload.
- Rule B — No nesting: never nest code fences. If multiple code blocks are needed, send them as separate top-level blocks in the same message.
- Rule C — Inner examples: within narrative docs, use 4-space indentation, or non-exec fences labeled `text`, `example`, `pseudo`, or `console`. Do not use `bash`, `sh`, `zsh`, `python`, `js`, or `ts` in reference/theory docs.
- Rule D — Control tokens: control tokens (e.g., `END_OF_LOG`) live in Chat lane. If a literal token must appear in shell logs, print it with `printf`, not as a bare line.

1) Mode switch (explicit)
- Default: Chat mode.
- Terminal mode (on request): reply with one fenced `bash` block only (no preface/epilogue). All notes appear as `#` comments inside the block.

2) Shell lane contract (when Terminal mode is on)
- Start with `set -Eeuo pipefail` and a safe `trap`.
- Guard checks with `if ! …; then …; fi`.
- Use heredocs for file writes.
- Forbidden: plain text labels (e.g., `sanity:`), mixed languages, placeholders, bare control tokens, RNL outside `#` comments.

3) Terminal paste hygiene & heredoc safety (RCA-backed rules)
- Enable bracketed paste on operator machines to make pastes atomic.
  - Operator setup:
      - Add to `~/.inputrc`:  
        (four spaces) set enable-bracketed-paste on
      - Reload:  
        (four spaces) bind -f ~/.inputrc
- Prefer the code-block copy button in ChatGPT; avoid mouse-drag selection or right-click paste that can chunk input.
- Two-step heredoc pattern for long scripts:
  - Step 1: write the script file via heredoc (opener/closer on their own lines, no trailing spaces).
  - Step 2: `bash -n` then execute it.
- Avoid process substitution (`< <( … )`) in long pastes; use temp files instead.
- Keep long deliveries under ~100 lines per block; otherwise use small-chunk mode (≤25 lines per chunk) or the two-step heredoc pattern.

4) Docs fence policy (reference/theory)
- All fenced blocks in `docs/reference` and `docs/theory` must use non-exec fences (`text`/`example`/`pseudo`/`console`) or 4-space indentation.
- Each such file should begin with a two-line disclaimer:
  - `> ⚠️ Examples only — not runnable`
  - `> This document contains illustrative/math/pseudo code. Do not execute in production.`
- A pre-commit linter must block `bash`/`sh`/`zsh`/`python`/`javascript`/`js`/`ts`/`typescript` fences in those directories.

5) Acceptance checklist (per delivery)
- One top-level `bash` block only in Terminal mode; no prose before/after.
- No nested code fences; inner examples use 4-space indentation or non-exec fences.
- Heredoc delimiters exact and on their own lines; no trailing spaces.
- No process substitution in long pastes; temp files used where needed.
- If scripts write scripts: validate first (`bash -n file`) before execution.

6) RNL scope limiter
- RNL hints are allowed in Chat lane or as `#` comments inside the shell block. Never emit RNL as a bare line in Terminal mode.

7) Handoff / reports
- In Chat lane, use normal prose and include the literal `END_OF_LOG` only when requested.
- In Terminal mode, if logs must contain it: `printf 'END_OF_LOG\n'` inside the bash block.

Appendix — RCA (why these rules exist)
- Two failures were traced to prompt text and line wraps interleaving with long pastes, corrupting heredocs, splitting `trap`/function lines, and tearing tokens like `< <(`. With bracketed paste off and long multi-line payloads, Bash reported downstream syntax errors (e.g., “unexpected token '('”). The policies above remove those failure modes by reserving fences, separating lanes, hardening paste technique, and limiting executable fence types in documentation.

0.2) Known environment quirks (WSL/Podman/RVM) — paste- & DB-friendly defaults
- **Avoid `set -u` in long multi-line pastes.** RVM shells can hook nounset (`rvm_bash_nounset`) and crash blocks.  
  - Default to: `set -Ee -o pipefail`  
  - If `-u` is required, briefly disable around engine/exec calls:  
        set +u; podman start ... || true; set -u
- **NUL-safe pipelines.** When consuming `git ls-files -z`, never stuff NULs into a plain var. Use arrays:  
        mapfile -d '' -t FILES < <(git ls-files -z -- '*.bak')
- **Guard empty arrays.** Before operations like `git rm --cached -- "${arr[@]}"`, check length:  
        ((${#arr[@]})) && git rm --cached -- "${arr[@]}"
- **Echo/export safety with unset vars.** When printing example commands that include `${VARS}`, single-quote the line to avoid expansion or `-u` failures:  
        printf '%s\n' 'export DATABASE_URL="postgresql://.../${POSTGRES_DB}"'
- **Heredoc safety.** Ensure the closing token is alone on its own line (no spaces). If a heredoc hangs, press Ctrl+C and rewrite the file in a fresh heredoc.
- **Bracketed paste must be enabled** on operator machines (Section 3). This prevents torn lines like `-Eeuo pipefail` splitting across paste boundaries.
- **IPv4 for localhost.** Prefer `127.0.0.1` over `localhost` to dodge IPv6 oddities in some WSL/container combos.
- **Compose & secrets.** Use `${POSTGRES_PASSWORD}` interpolation in compose; keep `.env` untracked; integration tests must read from env and may skip if unset.
- **psql UX.** Cancel partial input with Ctrl+C; exit with `\q`. To clear the screen inside `psql`: `\! clear`.
- **Dev DB helpers.** Use the Make targets instead of pasting:  
      make db-up      # start db (podman/docker)  
      make db-psql    # open psql (\q to exit)  
      make test-db    # run integration test  
      make db-logs    # tail logs  
      make db-down    # stop db
---

## Addendum: Paste Hygiene, Podman-on-WSL, and Progress Checklists

**Paste Hygiene**
    Enable bracketed paste:
        set enable-bracketed-paste on
    Prefer one-liners for ops; for long scripts use two-step heredocs:
        1) write file via heredoc (opener/closer on their own lines)
        2) bash -n file && bash file
    Avoid “smart quotes”; keep ASCII quotes only.

**Podman on WSL/Linux**
    Use Podman directly (no `podman machine`). Expose ports 9000/9001 for MinIO.
    For macOS/Windows hosts (no WSL), `podman machine` is required.

**MinIO Dev Pattern**
    Buckets: darf-originals, darf-derived, darf-reports (private + versioned).
    Access: service user `darf-ingester` with darf-ingest-rw policy (RW, no delete).
    Encryption: SSE-S3 deferred until KMS (KES or Vault) is configured.

**Progress Checklists (icon units)**
    ✅ = completed unit, ⬜ = pending unit, use counts for effort
    Example:
        ✅ 1× prereqs
        ✅ 1× service user
        ⬜ 2× ingestion tasks (EE, anchoring)

**PR Discipline**
    Do not push to main. Create a branch, push, and open a PR.

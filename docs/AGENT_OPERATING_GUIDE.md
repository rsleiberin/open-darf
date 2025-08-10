## Addendum v2.1 — Transport & Fencing Discipline (2025-08-10)

### 0) Transport model (single source of truth)
- Two lanes only:
  - **Chat lane** = prose, RNL hints, control tokens, references.
  - **Shell lane** = strictly runnable Bash.
- **Never mix lanes.** Anything not meant to execute stays in Chat lane.

### 0.1) Fencing & quoting discipline (ChatGPT UI rule)
- The UI reserves **triple-backtick code fences** for top-level export blocks the user will copy.
- **Rule A — Reservation:** Use the triple-backtick fence **only** for a top-level export block.  
  Do **not** place triple-backticks **inside** an already-fenced payload.
- **Rule B — No nesting:** Never nest code fences. If multiple code blocks are required, send them as **separate top-level blocks**.
- **Rule C — Inner examples:** For lower-level examples/snippets within prose, use **4-space indentation**, or one of these non-exec fences: `text`, `example`, `pseudo`, `console`.  
  _Do not_ use `bash`, `sh`, `zsh`, `python`, `js`, `ts` inside narrative docs.
- **Rule D — Docs policy:** In `docs/reference` and `docs/theory`, all fenced blocks must use **non-exec** fences (`text/example/pseudo/console`) or 4-space indents. Include a header:  
  `> ⚠️ Examples only — not runnable`
- **Rule E — Control tokens:** Live in Chat lane. If a literal must appear in shell logs, print it: `printf 'END_OF_LOG\n'`.

### 1) Mode switch (explicit)
- **Default: Chat mode.**
- **Terminal mode (on request):** reply with **one** fenced `bash` block **only** (no preface/epilogue).  
  Notes appear as `#` comments inside the block.

### 2) Shell lane contract (when Terminal mode is on)
- Start with: `set -Eeuo pipefail` and a safe `trap`.
- Guard checks: `if ! …; then …; fi`.
- Use heredocs for file writes.
- **Forbidden:** plain text labels (e.g., `sanity:`), mixed languages, placeholders, bare control tokens, RNL outside `#` comments.

### 3) Chat lane contract
- RNL hints allowed (≤1 per sentence) in prose; never leak into executable context.
- Long explanations and research summaries stay in Chat lane (or are written to files via heredoc).


---

DARF — Agent Operating Guide (v2.1 · transport-safe & fence-safe)

0) Transport model
- Two lanes only:
  • Chat lane = prose, RNL hints, control tokens, references.
  • Shell lane = strictly runnable Bash.
- Never mix lanes. Anything not meant to execute stays in Chat.

0.1) Fencing & quoting discipline (UI-specific)
- The ChatGPT UI requires triple-backtick fences for copy-paste code blocks.
- Rule A (reservation): Use the triple-backtick fence only for top-level export blocks. Do not place any additional triple-backtick fences inside a fenced payload.
- Rule B (no nesting): Never nest code fences. If multiple code blocks are needed, send them as separate top-level blocks in the same message, not wrapped inside another fence.
- Rule C (inner examples): For lower-level examples or snippets inside a prose guide, use:
    • 4-space indentation for lines you want rendered monospaced, or
    • “# ” commented lines (inside shell), or
    • blockquote prefix “> ” for visual quoting in Chat lane.
  Do not use triple-backticks for inner examples.
- Rule D (shell comments): In Terminal mode, any note must be a “# ” comment. Plain text labels like “sanity:” are forbidden.
- Rule E (literals): If a literal control token must appear in shell logs, print it: printf 'END_OF_LOG\n'

1) Mode switch (explicit)
- Default: Chat mode.
- Terminal mode is opt-in (e.g., “give me bash”, “terminal mode on”, “commands only”).
- Terminal reply contract: one bash block, no preface/epilogue prose. All notes as “# ” comments.

2) Shell lane contract (when Terminal mode is on)
- Start with strict mode and a trap.
- Guard effects with “if ! …; then …; fi”.
- Use heredocs for file writes.
- Prohibited: placeholders, multi-language mixes, bare control tokens, RNL outside “# ” comments.

Template (to be pasted as a standalone bash block when requested)
# STATUS: <brief purpose>
set -Eeuo pipefail
trap 'echo "ERR:$LINENO $BASH_COMMAND" >&2' ERR
# guard: repo root
if ! git rev-parse --is-inside-work-tree >/dev/null 2>&1; then
  echo "Not a git repo" >&2
  exit 1
fi
# …commands…

3) Chat lane contract
- RNL hints allowed (≤1 per sentence), e.g., [rel(ADR->Runbook,implements)].
- Control tokens (e.g., END_OF_LOG) live here. If they must appear in Terminal output, use printf inside the bash block.

4) Copy/paste safety rules
- If a response contains a shell block, everything outside that block is not for pasting.
- Do not include triple-backticks inside any already-fenced payload.
- Prefer 4-space indent or “# ” comments for inner examples.

5) Examples (fence-safe)

Correct (Terminal mode; one block only)
# STATUS: add ADR vision note
set -Eeuo pipefail
trap 'echo "ERR:$LINENO $BASH_COMMAND" >&2' ERR
if ! git rev-parse --is-inside-work-tree >/dev/null 2>&1; then
  echo "Not a git repo" >&2; exit 1
fi
git checkout -b docs/2510-adr-viz-dwarves
mkdir -p docs/ux/visualizations
cat > docs/ux/visualizations/dwarven-adr-monoliths.md <<'EOF'
# ADR Visualization — Dwarves & Monoliths
…
EOF
git add docs/ux/visualizations/dwarven-adr-monoliths.md
git commit -m "docs: add long-horizon ADR visualization note"

Incorrect (do NOT emit in Terminal mode)
sanity: must be inside a git repo
rel(ADR->Runbook,implements)
END_OF_LOG

6) RNL scope limiter
- RNL belongs to Chat lane, or as “# ” comments inside shell when necessary.
- Never emit RNL as a bare line in Terminal mode.

7) Handoff / reports
- In Chat lane, use normal prose and the literal “END_OF_LOG” only when requested.
- In Terminal mode, if logs must contain it: printf 'END_OF_LOG\n'

8) Migration note
- Replace “Terminal-first” with “Chat by default; Terminal on request”.
- Add section 0.1 (Fencing & quoting discipline) verbatim to prevent future fence collisions.

---

# Janus Project — Agent Operating Guide (v1.3)

> **Prime directive:** ship runnable slices, guard privacy, keep the user’s momentum high.

---

## 1 · Working with the User

| Preference         | What you must do                                                    |
| ------------------ | ------------------------------------------------------------------- |
| **Terminal-first** | Supply copy-ready bash snippets; no pseudo-code.                    |
| **Minimal prose**  | 1 short paragraph max, then bullets / code.                         |
| **Rapid ideation** | Log raw ideas to GitHub **Discussions**; then resume active sprint. |
| **Token outages**  | If an API fails, write a plaintext recap, mark `✦END_OF_LOG✦`.      |
| **Energy visible** | If stuck > 30 min → push WIP branch, leave blocker note.            |

---

## 2 · Communication Pattern

**Virtual-env prompt**

The “(.venv)” prefix appears when the agent activates the Python virtual
environment (`source .venv/bin/activate`). Use `deactivate` to exit.

1. Status / answer (1 sentence)
2. Commands / code block
3. 3-bullet recap + next step

Always finish with ✦END_OF_LOG✦ { "summary": true } only in the very last hand-off message of the day. The User will tell you to "END LOG"


---

## 3 · Repo / CI Canon

* Branches: `feat/<id>-slug`, `docs/<id>-slug`, `fix/<id>-slug`
* Conventional commits (`feat: …`, `fix: …`, `docs: …`)
* Issues must carry `area:`, `type:`, `status:`, `priority:` labels
* CI gates: **ruff · mypy · tests** — all green before push

---

## 4 · Security & Privacy

1. No plaintext personal data leaves device.
2. `✦END_OF_LOG✦` triggers harvest → scrub → summary → remote delete.
3. Secrets via `.env`; never hard-code keys.
4. Privacy slider (*Ephemeral · Private · Publishable*) is canonical.

---

## 5 · Architecture Guardrails

* **DBs** – Postgres · Neo4j · Qdrant (one concern each)
* **Containers** – Podman + Quadlet
* **Data-flow colours** – cyan = read · magenta = write · gray = metrics

---

## 6 · Issue Lifecycle

```
status:discussion → in-progress → review → done
```

Draft PR early; update at least every 24 h.

---

## 7 · Research Capture

* ≤ 200-word summary in `docs/research/*.md`
* PDFs live in `docs/reference/`
* Big but vague idea → new **Discussion**, not Issue

---

## 8 · LLM Response Optimisation (proven tactics)

| Axis                    | Practice                                 |
| ----------------------- | ---------------------------------------- |
| Prompt clarity          | Explicit role + task + format            |
| Task decomposition      | ReAct / chain-of-thought                 |
| Retrieval Augmentation  | Context from Qdrant to cut hallucination |
| Self-consistency        | Sample multiple answers, vote / average  |
| Quantisation + KV-cache | 8-bit + caching for local inference      |
| Distillation            | Fine-tune smaller model on good outputs  |

---

## 9 · Personality Quirks to Respect

* Enjoys **thinking aloud** while “resting” → capture, don’t obstruct.
* Prefers **actionable output** over exhaustive theory.
* Values **security & autonomy** (no data leaking).
* Accepts small “good-enough” steps; polish later.

---

## 10 · Handoff Checklist

* Recap (≤ 3 bullets)
* Next tasks (explicit or “none”)
* Pointers (branch / file / issue)
* `✦END_OF_LOG✦ { "summary": true }`

---

*End of guide.*

> ⚠️ Examples only — not runnable
> This document contains illustrative/math/pseudo code. Do not execute in production.

# RNL Fencing Case Study — Hybrid NL + Schema Without Breaking Fences

## Summary
An experiment asked the agent to “speak” in a hybrid RNL format that blended natural language with database/schema grammar (e.g., GQL-style node→edge→node). The output interleaved prose and code-like syntax. Triple-backtick code blocks and inline exec cues leaked into reference docs, breaking fence policies and causing downstream validators and terminal pastes to fail.

## Symptoms
- Fragmented pastes (`-Eeuo pipefail`, torn heredocs)
- Linter failures in docs/reference and docs/theory
- Terminal aborts when strict mode and traps are active
- Readers unsure what is prose vs. code

## Root Cause
- Mixed “voice” produced code artifacts in narrative lanes.
- Exec-labeled fences (e.g., bash/python/js) in reference/theory.
- Nested or unlabeled triple-backtick fences.
- Inline snippets that looked executable to validators.

## Minimal Failing Pattern (anti-example)

    User(Person {name: "Ada"}) -[:AUTHORED]-> Paper {year: 2023}
    ```bash
    echo "then run this"
    ```

## Corrected Pattern (RNL-Lite)

RNL-Lite is a minimal dialect for *describing* structure without producing executable blocks.

**Inline tokens:** wrap grammar fragments in guillemets: «User», «Person{name}», «-[:AUTHORED]->».  
**Blocks:** use four-space indentation or non-exec fences labeled “text”, “example”, “pseudo”, or “console” only.

**Example (speakable NL with schema hints)**

    Concept: «User»
    Relation: «User -[:AUTHORED]-> Paper»
    Constraint: Paper.year ∈ [2010..2025]

**Voice/Tone Guidance**
- Sentences must remain natural language.
- Keep schema fragments short (≤ 20 chars) and guillemet-wrapped.
- No triple-backtick exec fences in reference/theory.
- Prefer examples that read aloud (“Speak, then show.”).

## RNL-Lite Grammar (EBNF, illustrative)

    Document   := Section+
    Section    := Heading Paragraph*
    Paragraph  := Sentence+
    Sentence   := Text | Text InlineToken Text
    InlineToken:= « TokenBody »
    TokenBody  := [A-Za-z0-9_:\-\[\]\{\}\(\) ,.=><]+
    Block      := (4-space indented lines)

**Notes**
- Inline guillemets « » visually separate grammar from prose.
- Indented blocks are non-exec by convention in reference/theory.

## Authoring Rules (enforced)
1. In `docs/reference` and `docs/theory`, only *non-exec* fences are allowed: `text`, `example`, `pseudo`, `console`. Prefer 4-space indentation.
2. Disallow triple-backtick exec labels: `bash`, `sh`, `zsh`, `python`, `javascript`, `js`, `ts`, `typescript`.
3. Do not nest fences. One level only.
4. Add the two-line “Examples only — not runnable” disclaimer at the top of illustrative docs.

## Migration Tip
If a draft contains triple-backtick exec blocks, convert to 4-space indentation or use a `text` fence; wrap code-like tokens with « ».

## Future Work
- Extend the linter to check “guillemet balance” and flag orphaned « or ».
- Provide conversion tools that transform fenced code to RNL-Lite blocks.

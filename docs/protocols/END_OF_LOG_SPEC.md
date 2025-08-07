# END-OF-LOG Trigger Specification

**Purpose** – Signal that an LLM dialogue has ended, request a self-contained summary, then invoke the Janus security pipeline to harvest, scrub and delete the raw log.

```jsonc
✦END_OF_LOG✦ {
  "summary":        true,          // produce chronological recap
  "include_inputs": true,          // include user prompts
  "include_outputs": true,         // include agent answers
  "format":         "markdown",    // headings + bullets
  "max_tokens":     300,           // keep recap compact
  "post_action":    "scrub_remote" // run harvester → scrubber → delete
}
````

### Field semantics

| Key               | Meaning                                          |
| ----------------- | ------------------------------------------------ |
| `summary`         | Generate recap if `true`.                        |
| `include_inputs`  | Include sanitised user messages.                 |
| `include_outputs` | Include assistant responses.                     |
| `format`          | Output style; default `markdown`.                |
| `max_tokens`      | Hard ceiling for recap length.                   |
| `post_action`     | `"scrub_remote"` triggers the security pipeline. |

### Agent obligations

1. Stop reasoning; emit only the recap.
2. Respect `max_tokens` & `format`.
3. Perform no further external calls after summary.

*Version 1.0 · 2025-08-07*

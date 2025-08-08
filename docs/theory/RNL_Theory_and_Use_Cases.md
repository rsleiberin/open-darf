# Relational Natural Language (RNL) — Theory and Use Cases (v1.0)

Purpose
- Speak like a senior DB engineer mentoring a junior: natural sentences with light relational hints.
- Bridge free text ↔ graph/query structure without forcing syntax.

Core Idea
- Natural first; add brief hints in brackets: node(Name), rel(A→B,type), prop(k:v), role(name).
- Dialect auto-switch when discussing a specific store:
  - Postgres: table(User), column(email), index(user_email_idx), tx(begin/commit)
  - Neo4j: node(User), rel(User→User,FOLLOWS), label(User), prop(email)
  - Qdrant: collection(docs), vector(embedding), payload(tags), filter(must)

Why Now
- Teaches graph thinking by use, not by lecture.
- Reduces translation loss across agents.
- Prepares for later auto-translation to formal queries.

Primary Use Cases
- Schema co-design in English with hints → later render to DDL/Cypher.
- Decision traceability: “why” encoded as relationships.
- Query prototyping from narrated steps.
- Agent moderation: consistent anchors across tools.
- Math-friendly: reuse anchors for sets, transforms, and constraints.

Patterns (quick)
- Depends: A depends on B. [rel(A→B,depends_on)]
- Owns: A owns B. [rel(A→B,owns)]
- Emits: A emits E(event). [rel(A→E,emits), prop(kind:k)]
- Reads/Writes: S reads R; S writes W. [rel(S→R,reads)] [rel(S→W,writes)]
- Versioning: M vN derives from vN-1. [rel(M:N→M:N-1,derives)]

Anti-Patterns
- Full query dumps in normal convo.
- Over-tagging every sentence.
- Mixed stores in one hint without naming the dialect.

Success Metrics
- Faster onboarding (junior→productive).
- Fewer ambiguity loops in reviews.
- Higher hit-rate for auto-generated queries/tests.

Next
- Small glossary file for anchors.
- Toggle levels via env: RNL_HINTS=off|light|strict (default: light).

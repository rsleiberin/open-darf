# Relational Natural Language (RNL) — Theory & Use Cases (v1.1)

## Purpose
A human-first way to speak like a senior DB engineer mentoring a junior: natural sentences with one light relational hint, so conversations translate into queries later without forcing syntax now.

## Core primitives (ASCII, v0.1)
node(Name) · rel(A->B,type) · prop(key:value) · role(name)

## Hint levels
L0 off · L1 light (default, ≤1 hint/sentence) · L2 structured · L3 query-ready (on request)

## Dialect switching (auto when named or implied)
Postgres: table(User), column(email), index(user_email_idx), tx(begin/commit), constraint(unique)
Neo4j: node(User), rel(User->Doc,AUTHORED), label(User), prop(email)
Qdrant: collection(docs), vector(embedding), payload(tags), filter(must)

## Utterance shape (for decompression/learning)
Context → Action/Claim → RNL Hint → Evidence/Pointer → Next

## Why now
- Teaches graph thinking by use, not lecture.
- Reduces ambiguity across agents.
- Sets up later auto-translation to queries/tests.

## Primary use cases
- PR descriptions/reviews, ADRs, end-of-PR reports
- Schema co-design in English with hints → DDL/Cypher later
- Decision traceability (“why” as relations)
- Query prototyping from narrated steps

## Anti-patterns
Over-tagging; mixed stores in one hint without naming the dialect; dumping full query syntax unasked; wrapping control tokens in fences.

## Success metrics
Faster onboarding; fewer ambiguity loops; higher hit-rate for auto-generated queries/tests.

## Parking lot (future v0.2)
event(), version(), set(), map(), constraint() — keep them out of v0.1 until patterns stabilize.

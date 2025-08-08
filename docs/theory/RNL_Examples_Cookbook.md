# RNL Examples Cookbook (v1.0)

Format per item: Natural · Hint · Decompressed

1) Distributed dependency
- Natural: The ingest service can’t start until configs are loaded.
- Hint: [rel(Ingest->ConfigLoader,depends_on)]
- Decompressed: Treat it as an edge; diagnose ConfigLoader first when ingest stalls.

2) Event sourcing
- Natural: We keep an immutable log and rebuild state when needed.
- Hint: [rel(App->EventLog,reads), rel(App->State,derives)]
- Decompressed: Replay events should reproduce state if handlers are deterministic.

3) Privacy erasure with proof
- Natural: On erasure, delete references and keep a proof.
- Hint: [rel(User->Data,erasure), prop(proof:deletion_hash)]
- Decompressed: Proof shows action occurred without revealing the data.

4) Version lineage
- Natural: Model v4 derives from v3.
- Hint: [rel(Model:v4->Model:v3,derives)]
- Decompressed: Keep parent->child chains for audits and rollbacks.

5) Safety cascade
- Natural: Orchestrator must halt if queues saturate.
- Hint: [rel(Orchestrator->Queue,observes), rel(Orchestrator->Orchestrator,halts_on)]
- Decompressed: Backpressure trips a circuit breaker.

6) Schema intent (Neo4j)
- Natural: Authors write documents; documents carry topics.
- Hint: [rel(Author->Document,AUTHORED), rel(Document->Topic,tags)]
- Decompressed: Queries can walk Author->Document->Topic.

7) Rollups (Postgres)
- Natural: Store raw ticks; build hourly rollups.
- Hint: [rel(Ticks->Rollups,aggregates), prop(window:1h)]
- Decompressed: Validate rollups against raw slices.

8) Vector search (Qdrant)
- Natural: Similar docs but only within allowed projects.
- Hint: [rel(Query->Documents,similar_to), prop(filter:project_allowlist)]
- Decompressed: Similarity is constrained by payload filters.

9) ZK compliance
- Natural: Verify age without birthdate.
- Hint: [rel(User->Verifier,proves), prop(predicate:age>=18)]
- Decompressed: Verifier learns predicate outcome only.

10) CI gates
- Natural: Deploy only if tests and policies pass.
- Hint: [rel(Deploy->Tests,depends_on), rel(Deploy->Policy,depends_on)]
- Decompressed: Deploy node fans in from Tests and Policy.

11) Risk limits
- Natural: Halt trading if drawdown >5% in a day.
- Hint: [rel(RiskEngine->Trader,halts_on), prop(rule:drawdown>5%/day)]
- Decompressed: Metric trigger enforces an immediate stop.

12) Data lineage
- Natural: A forecast’s trust follows its features.
- Hint: [rel(Forecast->FeatureSet,derives), rel(FeatureSet->DataSource,reads)]
- Decompressed: Trust rolls back along derives and reads.

13) Least privilege
- Natural: Summarizer can read docs, not secrets.
- Hint: [rel(Summarizer->Document,reads), rel(Summarizer->Secret,denied)]
- Decompressed: Edges expose posture; scanners can audit.

14) Tagging as mapping
- Natural: The tagger maps documents to topics.
- Hint: [rel(Tagger->Document,reads), rel(Document->Topic,tags), role(tagger)]
- Decompressed: Function-like behavior without math notation.

15) Release narrative
- Natural: Replace local disk with S3; add encryption at rest.
- Hint: [rel(App->S3,uses), rel(S3->KMS,encrypts_with)]
- Decompressed: Two edges capture the change and posture.

16) Conflict resolution
- Natural: Prefer proposals that satisfy constraints.
- Hint: [rel(ProposalA->Policy,satisfies), rel(ProposalB->Policy,violates)]
- Decompressed: Arbitration chooses satisfies over violates.

17) Post-mortem governance
- Natural: After 30 days no heartbeat, lock writes and tombstone.
- Hint: [rel(Heartbeat->Agent,monitors), rel(Agent->Writes,disabled_on), prop(threshold:30d)]
- Decompressed: Monitor flips a control edge on threshold.

18) Human approval
- Natural: High-risk actions need a human OK.
- Hint: [rel(Action->Human,requires_approval)]
- Decompressed: Approval edge gates execution.

19) Onboarding map
- Natural: Show where a feature reads from and writes to.
- Hint: [rel(Feature->Input,reads), rel(Feature->Output,writes)]
- Decompressed: Two edges give a mental map fast.

20) Dialect switch (quick)
- Postgres: Unique email. [rel(UserTable->Email,constraint), prop(type:unique)]
- Neo4j: Follow edges. [rel(User->User,FOLLOWS)]
- Qdrant: Filtered similarity. [rel(Query->Documents,similar_to), prop(filter:tag=legal)]

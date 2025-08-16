---------------------------- MODULE CA_SpanAuthorization ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Users, Spans, Ops
VARIABLES affects, auth, revoked, epoch

TypeInvariant ==
  /\ affects \in [Ops -> SUBSET Spans]
  /\ auth    \in [Users -> [Ops -> SUBSET Spans]]
  /\ revoked \in [Users -> SUBSET Spans]
  /\ epoch \in Nat

\* Small-state bound for Class A runs
BoundEpoch == epoch <= 1

Init ==
  /\ epoch = 0
  /\ affects = [op \in Ops |-> Spans]
  /\ auth    = [u \in Users |-> [op \in Ops |-> affects[op]]]
  /\ revoked = [u \in Users |-> {}]

Apply(u, op, s) ==
  /\ u \in Users /\ op \in Ops /\ s \in affects[op]
  /\ s \in auth[u][op]
  /\ s \notin revoked[u]
  /\ epoch' = epoch + 1
  /\ UNCHANGED <<affects, auth, revoked>>

Next ==
  \/ \E u \in Users, op \in Ops, s \in Spans: Apply(u, op, s)
  \/ UNCHANGED <<affects, auth, revoked, epoch>>

ExplicitAuthorizationInv ==
  \A u \in Users, op \in Ops:
    auth[u][op] \subseteq affects[op] /\ revoked[u] = {}

BadEAInv == ~ExplicitAuthorizationInv

Spec == Init /\ [][Next]_<<affects,auth,revoked,epoch>>
=============================================================================

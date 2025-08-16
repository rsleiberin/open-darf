---------------------------- MODULE CA_SpanPreservesConstraints ----------------------------
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Users, Spans, Constraints, Nil
VARIABLES owner, constr, src, epoch

TypeInvariant ==
  /\ owner \in [Spans -> Users]
  /\ constr \in [Spans -> SUBSET Constraints]
  /\ src \in [Spans -> (Spans \cup {Nil})]
  /\ epoch \in Nat

Init ==
  /\ epoch = 0
  /\ owner \in [Spans -> Users]
  /\ constr \in [Spans -> SUBSET Constraints]
  /\ src = [s \in Spans |-> Nil]

Derive(s, s2) ==
  /\ s \in Spans /\ s2 \in Spans /\ s # s2
  /\ src[s2] = Nil
  /\ LET cs == CHOOSE X \in SUBSET constr[s] : TRUE IN
     /\ owner'  = [owner  EXCEPT ![s2] = owner[s]]
     /\ constr' = [constr EXCEPT ![s2] = cs]
     /\ src'    = [src    EXCEPT ![s2] = s]
     /\ epoch'  = epoch + 1

Next ==
  \/ \E s \in Spans, s2 \in Spans: Derive(s, s2)
  \/ UNCHANGED <<owner, constr, src, epoch>>

ConstitutionalPreservationInv ==
  \A s \in Spans:
    src[s] # Nil =>
      /\ constr[s] \subseteq constr[src[s]]
      /\ owner[s]  = owner[src[s]]

BadInv == ~ConstitutionalPreservationInv

Spec == Init /\ [][Next]_<<owner,constr,src,epoch>>
=============================================================================

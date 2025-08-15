------------------------------ MODULE CA_CapabilityEnhancement ------------------------------
EXTENDS FiniteSets

CONSTANTS Users, Caps

VARIABLES cap, prevCap
\* cap: Users -> SUBSET Caps
\* prevCap: snapshot of previous caps (for monotonicity check)

TypeInvariant ==
  /\ cap \in [Users -> SUBSET Caps]
  /\ prevCap \in [Users -> SUBSET Caps]

Init ==
  /\ cap = [u \in Users |-> {}]
  /\ prevCap = cap

Add(u, c) ==
  /\ u \in Users /\ c \in Caps
  /\ c \notin cap[u]
  /\ cap' = [cap EXCEPT ![u] = @ \cup {c}]
  /\ prevCap' = cap

Next ==
  ( \E u \in Users, c \in Caps : Add(u, c) )
  \/ UNCHANGED << cap, prevCap >>

CapabilityEnhancementInv ==
  \A u \in Users : prevCap[u] \subseteq cap[u]

Spec == Init /\ [] [Next]_<< cap, prevCap >>
================================================================================

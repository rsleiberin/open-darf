---- MODULE CA_TriStateCompleteness ----
EXTENDS Integers, TLC

CONSTANTS Requests
VARIABLES state, decision

States == {"ALLOW","DENY","INDETERMINATE"}

TypeInvariant ==
  /\ state \in [Requests -> BOOLEAN]
  /\ decision \in [Requests -> States]

Completeness ==
  \A r \in Requests: decision[r] \in States

NoIllegalState ==
  \A r \in Requests: ~(decision[r] \notin States)

Init ==
  /\ TypeInvariant

Next ==
  UNCHANGED <<state, decision>>

Spec == Init /\ [][Next]_<<state,decision>>

THEOREM TriStateOnly == Spec => [](Completeness /\ NoIllegalState)

====

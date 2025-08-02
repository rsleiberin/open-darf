---- MODULE CA_TriStateCompleteness ----
EXTENDS Integers, TLC
CONSTANTS Requests
VARIABLES decision

States == {"ALLOW", "DENY", "INDETERMINATE"}

TypeInvariant ==
  decision \in [Requests -> States]

Completeness ==
  \A r \in Requests: decision[r] \in States

NoIllegalState ==
  \A r \in Requests: decision[r] \in States

Init ==
  decision \in [Requests -> States]

Next ==
  \E r \in Requests:
    \E s \in States:
      decision' = [decision EXCEPT ![r] = s]

StateConstraint ==
  /\ TLCGet("level") <= 50
  /\ TLCGet("distinct") <= 5000

Spec == Init /\ [][Next]_<<decision>>

THEOREM TriStateCompleteness == Spec => [](Completeness /\ NoIllegalState)
====

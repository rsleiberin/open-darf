---- MODULE CA_DenyPrecedence ----
EXTENDS Integers, FiniteSets, TLC

CONSTANTS Resources, Participants
VARIABLES state

PrecedenceInvariant ==
  \A p \in Participants:
    \A r \in Resources:
      state[p][r] = "DENY" => (\A q \in Participants: state[q][r] # "ALLOW")

TypeInvariant ==
  state \in [Participants -> [Resources -> {"ALLOW","DENY","INDETERMINATE"}]]

\* Start with all INDETERMINATE to satisfy precedence invariant
Init ==
  state = [p \in Participants |-> [r \in Resources |-> "INDETERMINATE"]]

\* Allow transitions that maintain DENY precedence in both directions
Next ==
  \/ UNCHANGED state
  \/ \E p \in Participants, r \in Resources :
       /\ state[p][r] = "INDETERMINATE"
       /\ \/ /\ \A q \in Participants : state[q][r] # "ALLOW"  \* No one has ALLOW yet
             /\ state' = [state EXCEPT ![p][r] = "DENY"]
          \/ /\ \A q \in Participants : state[q][r] # "DENY"   \* No one has DENY yet
             /\ state' = [state EXCEPT ![p][r] = "ALLOW"]

Spec == Init /\ [][Next]_state

THEOREM TypeOk == Spec => []TypeInvariant
THEOREM DenyDominates == Spec => []PrecedenceInvariant
====

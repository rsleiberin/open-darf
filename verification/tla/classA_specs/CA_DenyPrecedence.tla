---- MODULE CA_DenyPrecedence ----
...DS Integers, FiniteSets, TLC

CONSTANTS Resources, Participants

VARIABLES state

(* --algorithm DenyPrecedence
variables state \in [Participants -> [Resources -> {"ALLOW","DENY","INDETERMINATE"}]];
begin
  Skip;
end algorithm; *)

PrecedenceInvariant ==
  \A p \in Participants:
    \A r \in Resources:
      state[p][r] = "DENY" => (\A q \in Participants: state[q][r] # "ALLOW")

TypeInvariant ==
  state \in [Participants -> [Resources -> {"ALLOW","DENY","INDETERMINATE"}]]

Init ==
  /\ TypeInvariant

Next ==
  UNCHANGED state

Spec == Init /\ [][Next]_state

THEOREM TypeOk == Spec => []TypeInvariant
THEOREM DenyDominates == Spec => []PrecedenceInvariant

====

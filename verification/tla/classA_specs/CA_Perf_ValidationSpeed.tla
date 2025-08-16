---------------------------- MODULE CA_Perf_ValidationSpeed ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Constraints, MaxValidationTime, SpecialConstraint, SlowConstraint
VARIABLES processed, lastCost

TypeInvariant ==
  processed \subseteq Constraints /\ lastCost \in Nat

Init ==
  /\ processed = {}
  /\ lastCost = 0

Cost(c) ==
  IF SlowConstraint /\ c = SpecialConstraint THEN MaxValidationTime + 1
  ELSE MaxValidationTime \div 10

Next ==
  \E c \in Constraints \ processed:
    /\ processed' = processed \cup {c}
    /\ lastCost' = Cost(c)

Spec == Init /\ [][Next]_<<processed, lastCost>>
ValidationBoundInv == lastCost <= MaxValidationTime
=============================================================================

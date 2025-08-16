---------------------------- MODULE CA_Smoke ----------------------------
EXTENDS Naturals
VARIABLES epoch
Init == epoch = 0
Next == epoch' = epoch  \* stutter
TypeInvariant == epoch \in Nat
BadInv == epoch = 1
Spec == Init /\ [][Next]_<<epoch>>
=============================================================================

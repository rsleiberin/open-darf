------------------------------ MODULE CA_ConstCompliance ------------------------------
EXTENDS Naturals, FiniteSets
CONSTANTS Users, MaxVal
VARIABLES s, prevS
TypeInvariant == /\ s \in [Users -> 0..MaxVal] /\ prevS \in [Users -> 0..MaxVal]
Init == /\ s = [u \in Users |-> 0] /\ prevS = s
Apply(u) == /\ u \in Users /\ s[u] < MaxVal /\ s' = [s EXCEPT ![u] = s[u] + 1] /\ prevS' = s
Next == ( \E u \in Users : Apply(u) ) \/ UNCHANGED << s, prevS >>
SovereigntyPreservationInv == \A u \in Users : s[u] >= prevS[u]
Spec == Init /\ [] [Next]_<< s, prevS >>
================================================================================

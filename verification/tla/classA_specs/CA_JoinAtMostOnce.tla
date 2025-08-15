------------------------------ MODULE CA_JoinAtMostOnce ------------------------------
EXTENDS FiniteSets
CONSTANTS Nodes
VARIABLES joined
TypeInvariant == joined \in SUBSET Nodes
Init == joined = {}
Next == \E n \in Nodes \ joined : joined' = joined \cup {n} \/ UNCHANGED joined
JoinAtMostOnceInv == \A n \in Nodes : Cardinality(joined \cap {n}) \in {0,1}
Spec == Init /\ [] [Next]_<< joined >>
================================================================================

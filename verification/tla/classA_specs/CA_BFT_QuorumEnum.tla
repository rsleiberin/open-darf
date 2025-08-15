------------------------------ MODULE CA_BFT_QuorumEnum ------------------------------
EXTENDS Naturals, FiniteSets
CONSTANTS Nodes, QuorumThreshold
VARIABLES q1, q2
TypeInvariant == /\ q1 \in SUBSET Nodes /\ q2 \in SUBSET Nodes
Init == /\ q1 = {} /\ q2 = {}
Next == /\ q1' \in SUBSET Nodes /\ q2' \in SUBSET Nodes
QuorumIntersectionEnum == (Cardinality(q1) >= QuorumThreshold /\ Cardinality(q2) >= QuorumThreshold) => q1 \cap q2 # {}
Spec == Init /\ [] [Next]_<< q1, q2 >>
================================================================================

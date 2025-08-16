---------------------------- MODULE CA_ConstraintHierarchy ----------------------------
EXTENDS FiniteSets
CONSTANTS Constraints, ParentRel, ParentDeny, ChildAllow
VARIABLES epoch
Init == epoch = 0
Next == epoch' = epoch  \* stutter, static check
Spec == Init /\ [][Next]_epoch
IsChild(p,c) == <<p,c>> \in ParentRel
HierarchyConsistent == \A p,c \in Constraints:
  IsChild(p,c) /\ c \in ChildAllow /\ p \in ParentDeny => FALSE
TypeInvariant == epoch \in Nat
=============================================================================

---------------------------- MODULE CA_ConstraintHierarchy ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS
  Constraints,   \* small atom set
  Parent,        \* a constraint atom
  Child,         \* a constraint atom
  ParentDeny,    \* subset of Constraints
  ChildAllow     \* subset of Constraints

VARIABLES epoch
Init == epoch = 0
Next == epoch' = epoch  \* stutter; static check

ParentRel == {<<Parent, Child>>}
IsChild(p, c) == <<p, c>> \in ParentRel

HierarchyConsistent ==
  \A p, c \in Constraints:
    IsChild(p, c) /\ c \in ChildAllow /\ p \in ParentDeny => FALSE

TypeInvariant == epoch \in Nat
Spec == Init /\ [][Next]_epoch
=============================================================================

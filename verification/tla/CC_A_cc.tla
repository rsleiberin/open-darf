------------------------------ MODULE CC_A_cc ------------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS n1, n2, p1, p2, r1, r2
Nodes == {n1, n2}
Principals == {p1, p2}
Resources == {r1, r2}
MaxOperations == 5
Owner == [ n \in Nodes |-> IF n = n1 THEN p1 ELSE p2 ]

VARIABLES operations, policies, delegations, signatures
vars == <<operations, policies, delegations, signatures>>

CC == INSTANCE ConstitutionCore
  WITH Nodes <- Nodes, Principals <- Principals, Resources <- Resources,
       MaxOperations <- MaxOperations, Owner <- Owner,
       operations <- operations, policies <- policies,
       delegations <- delegations, signatures <- signatures

Spec == CC!Spec
Inv_SovA == CC!Inv_Sov
Inv_AuthA == CC!Inv_Auth
Inv_NoOverrideA == CC!Inv_NoOverride
Inv_DeleteSovereigntyA == CC!Inv_DeleteSovereignty
Inv_DeleteNoOverrideA == CC!Inv_DeleteNoOverride

(* Quick state-space constraint for fast checks (Class-A). *)
StateConstr ==
  /\ Cardinality(operations) <= 2
  /\ Cardinality(delegations) <= 1
====

\* Quick state-space constraint for fast checks (Class-A).

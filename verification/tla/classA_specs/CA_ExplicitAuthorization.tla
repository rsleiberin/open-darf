------------------------------ MODULE CA_ExplicitAuthorization ------------------------------
EXTENDS FiniteSets
CONSTANTS Users, Ops, AllowedUsers, AllowedOps
Grants == { [u |-> u, op |-> o] : u \in AllowedUsers, o \in AllowedOps }
VARIABLES applied
TypeInvariant == applied \in SUBSET [u: Users, op: Ops]
Init == applied = {}
Next == \E p \in Grants \ applied : applied' = applied \cup {p} \/ UNCHANGED applied
ExplicitAuthorizationInv == applied \subseteq Grants
Spec == Init /\ [] [Next]_<< applied >>
================================================================================

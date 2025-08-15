------------------------------ MODULE CA_RevocationAuthority_Weak ------------------------------
EXTENDS FiniteSets

CONSTANTS Users, Caps, Admins, InitU, InitC
InitGrants == { [u |-> InitU, cap |-> InitC] }

VARIABLES grants, prevGrants, actor

TypeInvariant ==
  /\ grants \in SUBSET [u: Users, cap: Caps]
  /\ prevGrants \in SUBSET [u: Users, cap: Caps]
  /\ actor \in Users

Init ==
  /\ grants = InitGrants
  /\ prevGrants = grants
  /\ actor \in Users

Grant(u, c) ==
  /\ u \in Users /\ c \in Caps
  /\ [u |-> u, cap |-> c] \notin grants
  /\ grants' = grants \cup { [u |-> u, cap |-> c] }
  /\ actor' = u
  /\ prevGrants' = grants

Revoke(u, p) ==
  /\ u \in Users /\ p \in grants
  /\ grants' = grants \ { p }          \* no admin guard
  /\ actor' = u
  /\ prevGrants' = grants

Next ==
  ( \E u \in Users, c \in Caps : Grant(u,c) )
  \/ ( \E u \in Users, p \in grants : Revoke(u,p) )
  \/ UNCHANGED << grants, prevGrants, actor >>

RevocationAuthorityInv ==
  (prevGrants \ grants = {}) \/ (actor \in Admins)

Spec == Init /\ [] [Next]_<< grants, prevGrants, actor >>
================================================================================

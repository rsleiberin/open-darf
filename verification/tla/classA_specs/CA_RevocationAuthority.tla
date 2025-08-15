------------------------------ MODULE CA_RevocationAuthority ------------------------------
EXTENDS FiniteSets

CONSTANTS Users, Caps, Admins, InitU, InitC
\* InitGrants is derived internally from simple atoms to avoid cfg record literals.
InitGrants == { [u |-> InitU, cap |-> InitC] }

VARIABLES grants, prevGrants, actor
\* grants ⊆ [u: Users, cap: Caps]
\* prevGrants = previous state's grants (for removal detection)
\* actor ∈ Users indicates who performed the last action

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
  /\ u \in Admins                     \* strong guard: only admins can revoke
  /\ grants' = grants \ { p }
  /\ actor' = u
  /\ prevGrants' = grants

Next ==
  ( \E u \in Users, c \in Caps : Grant(u,c) )
  \/ ( \E u \in Users, p \in grants : Revoke(u,p) )
  \/ UNCHANGED << grants, prevGrants, actor >>

\* If something was removed (prevGrants \ grants ≠ ∅), the actor must be an admin.
RevocationAuthorityInv ==
  (prevGrants \ grants = {}) \/ (actor \in Admins)

Spec == Init /\ [] [Next]_<< grants, prevGrants, actor >>
================================================================================

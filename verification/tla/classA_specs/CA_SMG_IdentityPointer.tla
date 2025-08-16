---------------------------- MODULE CA_SMG_IdentityPointer ----------------------------
EXTENDS Naturals, FiniteSets
CONSTANTS Users, AllowCoreMutation, MaxAux
VARIABLES idCore, idAux, prevCore

TypeInvariant ==
  /\ idCore \in [Users -> Nat]
  /\ idAux  \in [Users -> 0..MaxAux]
  /\ prevCore \in [Users -> Nat]

Init ==
  /\ idCore = [u \in Users |-> 0]
  /\ idAux  = [u \in Users |-> 0]
  /\ prevCore = idCore

AuxStep ==
  \E u \in Users:
    /\ idAux[u] < MaxAux
    /\ idCore' = idCore
    /\ idAux'  = [idAux EXCEPT ![u] = idAux[u] + 1]
    /\ prevCore' = idCore

CoreMutStep ==
  \E u \in Users:
    /\ AllowCoreMutation
    /\ idCore' = [idCore EXCEPT ![u] = idCore[u] + 1]
    /\ idAux'  = idAux
    /\ prevCore' = idCore

Next == AuxStep \/ CoreMutStep
Spec == Init /\ [][Next]_<<idCore, idAux, prevCore>>
IdentityPersistenceInv == \A u \in Users: idCore[u] = prevCore[u]
=============================================================================

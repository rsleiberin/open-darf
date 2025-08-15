------------------------------ MODULE CA_IdentityPersistence ------------------------------
EXTENDS Naturals, FiniteSets
CONSTANTS Users, MaxCore, MaxAux
VARIABLES id, prevCore
TypeInvariant == /\ id \in [Users -> [core: 0..MaxCore, aux: 0..MaxAux]] /\ prevCore \in [Users -> 0..MaxCore]
Init == /\ id = [u \in Users |-> [core |-> 0, aux |-> 0]] /\ prevCore = [u \in Users |-> id[u].core]
AuxInc(u) == /\ u \in Users /\ id[u].aux < MaxAux /\ id' = [id EXCEPT ![u].aux = @ + 1] /\ prevCore' = [v \in Users |-> id[v].core]
Next == ( \E u \in Users : AuxInc(u) ) \/ UNCHANGED << id, prevCore >>
IdentityPersistenceInv == \A u \in Users : id[u].core = prevCore[u]
Spec == Init /\ [] [Next]_<< id, prevCore >>
================================================================================

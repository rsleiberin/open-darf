---------------------------- MODULE CA_Neo4jConstraintSchema ----------------------------
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Users, Artifacts, CIDs
VARIABLES Owns, DerivedFrom, BackedBy, Revoked, epoch

TypeInvariant ==
  /\ Owns \in SUBSET (Users \X Artifacts)
  /\ DerivedFrom \in SUBSET (Artifacts \X Artifacts)
  /\ BackedBy \in SUBSET (Artifacts \X CIDs)
  /\ Revoked \in SUBSET (Users \X Artifacts)
  /\ epoch \in Nat

Init ==
  /\ epoch = 0
  /\ \E u0 \in Users, c0 \in CIDs:
       /\ Owns = ({u0} \X Artifacts)
       /\ DerivedFrom \in SUBSET (Artifacts \X Artifacts)
       /\ BackedBy = (Artifacts \X {c0})
       /\ Revoked = {}

Next == UNCHANGED <<Owns,DerivedFrom,BackedBy,Revoked,epoch>>

OwnershipPreservationInv ==
  \A a1, a2 \in Artifacts:
    <<a2, a1>> \in DerivedFrom =>
      \E u \in Users: <<u, a1>> \in Owns /\ <<u, a2>> \in Owns

TransparencyInv ==
  \A a \in Artifacts: \E c \in CIDs: <<a, c>> \in BackedBy

RevocationBlocksOpsInv ==
  \A u \in Users, a \in Artifacts:
    <<u, a>> \in Revoked => \A a2 \in Artifacts: <<a2, a>> \notin DerivedFrom

BadTransparencyInv == ~TransparencyInv

Spec == Init /\ [][Next]_<<Owns,DerivedFrom,BackedBy,Revoked,epoch>>
=============================================================================

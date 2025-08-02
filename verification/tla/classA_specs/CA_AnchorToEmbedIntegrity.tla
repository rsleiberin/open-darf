---------------------------- MODULE CA_AnchorToEmbedIntegrity ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Anchors, Embeds, Nil
VARIABLES backref, revokedA, epoch

TypeInvariant ==
  /\ backref \in [Embeds -> (Anchors \cup {Nil})]
  /\ revokedA \in SUBSET Anchors
  /\ epoch \in Nat

\* Bound the search to a tiny state space for Class A runs
BoundEpoch == epoch <= 1

Init ==
  /\ epoch = 0
  /\ backref = [e \in Embeds |-> Nil]
  /\ revokedA = {}

MakeEmbed(a,e) ==
  /\ a \in Anchors /\ e \in Embeds
  /\ backref[e] = Nil
  /\ a \notin revokedA
  /\ backref' = [backref EXCEPT ![e] = a]
  /\ revokedA' = revokedA
  /\ epoch' = epoch + 1

RevokeAnchor(a) ==
  /\ a \in Anchors
  /\ revokedA' = revokedA \cup {a}
  /\ backref' = [e \in Embeds |-> IF backref[e] = a THEN Nil ELSE backref[e]]
  /\ epoch' = epoch + 1

Next ==
  \/ \E a \in Anchors, e \in Embeds: MakeEmbed(a,e)
  \/ \E a \in Anchors: RevokeAnchor(a)
  \/ UNCHANGED <<backref,revokedA,epoch>>

IntegrityAndRollbackInv ==
  /\ \A e \in Embeds: backref[e] # Nil => backref[e] \notin revokedA
  /\ \A a \in revokedA, e \in Embeds: backref[e] # a

BadIntegrityInv == ~IntegrityAndRollbackInv

Spec == Init /\ [][Next]_<<backref,revokedA,epoch>>
=============================================================================

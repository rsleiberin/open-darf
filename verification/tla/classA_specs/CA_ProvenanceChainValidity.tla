---- MODULE CA_ProvenanceChainValidity ----
EXTENDS Integers, FiniteSets, TLC
CONSTANTS MaxArtifacts
VARIABLES Prov

Artifacts == 1..MaxArtifacts

TypeInvariant ==
  Prov \in [Artifacts -> SUBSET Artifacts]

Acyclic ==
  \A a \in Artifacts:
    a \notin Prov[a]

ChainValid ==
  \A a \in Artifacts:
    \A parent \in Prov[a]:
      parent \in Artifacts

Init ==
  Prov = [a \in Artifacts |-> {}]

Next ==
  \E artifact \in Artifacts:
    \E parent \in Artifacts:
      /\ parent # artifact
      /\ parent \notin Prov[artifact]
      /\ Prov' = [Prov EXCEPT ![artifact] = @ \cup {parent}]

StateConstraint ==
  /\ \A a \in Artifacts: Cardinality(Prov[a]) <= 2
  /\ TLCGet("level") <= 20
  /\ TLCGet("distinct") <= 5000

Spec == Init /\ [][Next]_Prov
====

---- MODULE CA_ProvenanceChainValidity ----
EXTENDS Integers, FiniteSets, TLC

CONSTANTS Entities, Artifacts, Parents

VARIABLES Prov

TypeInvariant ==
  Prov \in [Artifacts -> SUBSET Artifacts]

Acyclic ==
  \A a \in Artifacts:
    ~(a \in UNION { {b} \cup Prov[b] : b \in Prov[a] })

Init ==
  /\ TypeInvariant

Next ==
  UNCHANGED Prov

Spec == Init /\ [][Next]_Prov

THEOREM NoCycles == Spec => []Acyclic

====

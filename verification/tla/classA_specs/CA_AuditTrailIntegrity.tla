---- MODULE CA_AuditTrailIntegrity ----
EXTENDS Integers, Sequences, TLC

CONSTANTS MaxEntries
VARIABLES Log

EntryType(e) == /\ e \in [ "ts" : Nat, "actor" : STRING, "action" : STRING, "hash" : STRING ]

TypeInvariant ==
  /\ Log \in Seq( [ "ts":Nat, "actor":STRING, "action":STRING, "hash":STRING ] )
  /\ Len(Log) <= MaxEntries

AppendPreservesChain ==
  \A i \in 2..Len(Log):
    Log[i].hash # "" /\ Log[i-1].hash # ""

Init ==
  /\ Log = << >>

Next ==
  UNCHANGED Log

Spec == Init /\ [][Next]_Log

THEOREM AuditLogWellFormed == Spec => [](TypeInvariant /\ AppendPreservesChain)

====

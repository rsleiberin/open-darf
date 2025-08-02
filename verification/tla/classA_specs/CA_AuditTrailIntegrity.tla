---- MODULE CA_AuditTrailIntegrity ----
EXTENDS Integers, Sequences, TLC
CONSTANTS MaxEntries
VARIABLES Log

Timestamps == 1..3
Actors == {"usr", "sys"}
Actions == {"add", "del"}
Hashes == {"h1", "h2", ""}

LogEntry == [ts: Timestamps, actor: Actors, action: Actions, hash: Hashes]

TypeInvariant ==
  Log \in Seq(LogEntry)

AppendOnly ==
  \A i \in 1..Len(Log):
    Log[i].hash # ""

ChainIntegrity ==
  \A i \in 2..Len(Log):
    Log[i].ts >= Log[i-1].ts

Init ==
  Log = << >>

Next ==
  \/ /\ Len(Log) < MaxEntries
     /\ \E entry \in LogEntry:
          /\ entry.hash # ""
          /\ entry.ts >= (IF Len(Log) = 0 THEN 1 ELSE Log[Len(Log)].ts)
          /\ Log' = Append(Log, entry)
  \/ UNCHANGED Log

StateConstraint ==
  /\ Len(Log) <= 2
  /\ TLCGet("level") <= 10
  /\ TLCGet("distinct") <= 1000

Spec == Init /\ [][Next]_Log
====

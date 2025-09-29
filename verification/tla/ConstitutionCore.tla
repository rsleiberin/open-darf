---- MODULE ConstitutionCore ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Nodes, Principals, Resources, MaxOperations, Owner

VARIABLES operations, policies, delegations, signatures

Alphabet == {"create", "read", "modify", "delete"}

Hash(op) == ToString(op.id)

TypeOK ==
    /\ operations \subseteq [
        id: 1..MaxOperations,
        type: Alphabet,
        principal: Principals,
        resource: Resources,
        node: Nodes,
        timestamp: 0..MaxOperations,
        status: {"pending", "authorized", "denied"}
       ]
    /\ policies \in [Nodes -> SUBSET [
        principal: Principals,
        resource: Resources,
        permissions: SUBSET Alphabet
       ]]
    /\ delegations \subseteq [
        delegator: Principals,
        delegatee: Principals,
        resource: Resources,
        permissions: SUBSET Alphabet
       ]
    /\ signatures \in [1..MaxOperations -> STRING]

Authorized(node, principal) ==
    \E policy \in policies[node] :
        /\ policy.principal = principal
        /\ "create" \in policy.permissions

AuthorizedForOp(op) ==
    \/ Authorized(op.node, op.principal)
    \/ \E del \in delegations :
        /\ del.delegator = Owner
        /\ del.delegatee = op.principal
        /\ del.resource = op.resource
        /\ op.type \in del.permissions

Inv_Sov ==
    \A op \in operations :
        op.status = "authorized" =>
            \/ Authorized(op.node, op.principal)
            \/ \E del \in delegations :
                /\ del.delegator = Owner
                /\ del.delegatee = op.principal
                /\ op.type \in del.permissions

Inv_Auth ==
    \A op \in operations :
        op.status = "authorized" =>
            AuthorizedForOp(op)

Inv_NoOverride ==
    \A op1, op2 \in operations :
        (op1.resource = op2.resource /\ op1.id # op2.id) =>
            (op1.status = "denied" \/ op2.status = "denied" \/ op1.principal = op2.principal)

Inv_DeleteSovereignty ==
    \A op \in operations :
        (op.type = "delete" /\ op.status = "authorized") =>
            \/ op.principal = Owner
            \/ \E del \in delegations :
                /\ del.delegator = Owner
                /\ del.delegatee = op.principal
                /\ "delete" \in del.permissions
                /\ del.resource = op.resource

Inv_DeleteNoOverride ==
    \A op1, op2 \in operations :
        (op1.type = "delete" /\ op1.status = "authorized" /\ op1.resource = op2.resource) =>
            (op2.status = "denied" \/ op1.id = op2.id)

SafetyProperty ==
    /\ Inv_Sov
    /\ Inv_Auth
    /\ Inv_NoOverride
    /\ Inv_DeleteSovereignty
    /\ Inv_DeleteNoOverride

Init ==
    /\ operations = {}
    /\ policies = [n \in Nodes |-> {}]
    /\ delegations = {}
    /\ signatures = [i \in 1..MaxOperations |-> ""]

CreateOperation(principal, resource, node) ==
    /\ Cardinality(operations) < MaxOperations
    /\ ~\E op \in operations : op.type = "delete" /\ op.status = "authorized" /\ op.resource = resource
    /\ ~\E op \in operations : op.status = "authorized" /\ op.resource = resource /\ op.principal # principal
    /\ LET newOp == [
             id        |-> Cardinality(operations) + 1,
             type      |-> "create",
             principal |-> principal,
             resource  |-> resource,
             node      |-> node,
             timestamp |-> CHOOSE t \in 0..MaxOperations : TRUE,
             status    |-> IF Authorized(node, principal)
                           THEN "authorized" ELSE "denied"
         ]
       IN /\ operations' = operations \union {newOp}
          /\ signatures' =
               IF newOp.status = "authorized" /\ newOp.id <= MaxOperations
               THEN [signatures EXCEPT ![newOp.id] = Hash(newOp)]
               ELSE signatures
    /\ UNCHANGED <<policies, delegations>>

AddDelegation(delegator, delegatee, resource, perms) ==
    /\ delegator = Owner
    /\ LET newDelegation == [
             delegator   |-> delegator,
             delegatee   |-> delegatee,
             resource    |-> resource,
             permissions |-> perms
         ]
       IN delegations' = delegations \union {newDelegation}
    /\ UNCHANGED <<operations, policies, signatures>>

ModifyOperation(principal, resource, node) ==
    /\ Cardinality(operations) < MaxOperations
    /\ ~\E op \in operations : op.type = "delete" /\ op.status = "authorized" /\ op.resource = resource
    /\ ~\E op \in operations : op.status = "authorized" /\ op.resource = resource /\ op.principal # principal
    /\ LET newOp == [
             id        |-> Cardinality(operations) + 1,
             type      |-> "modify",
             principal |-> principal,
             resource  |-> resource,
             node      |-> node,
             timestamp |-> CHOOSE t \in 0..MaxOperations : TRUE,
             status    |-> IF AuthorizedForOp([
                              id |-> Cardinality(operations) + 1,
                              type |-> "modify",
                              principal |-> principal,
                              resource |-> resource,
                              node |-> node,
                              timestamp |-> CHOOSE t \in 0..MaxOperations : TRUE,
                              status |-> "pending"
                           ])
                           THEN "authorized" ELSE "denied"
         ]
       IN /\ operations' = operations \union {newOp}
          /\ signatures' =
               IF newOp.status = "authorized" /\ newOp.id <= MaxOperations
               THEN [signatures EXCEPT ![newOp.id] = Hash(newOp)]
               ELSE signatures
    /\ UNCHANGED <<policies, delegations>>

DeleteOperation(principal, resource, node) ==
    /\ Cardinality(operations) < MaxOperations
    /\ ~\E op \in operations : op.status = "authorized" /\ op.resource = resource
    /\ LET newOp == [
             id        |-> Cardinality(operations) + 1,
             type      |-> "delete",
             principal |-> principal,
             resource  |-> resource,
             node      |-> node,
             timestamp |-> CHOOSE t \in 0..MaxOperations : TRUE,
             status    |-> IF AuthorizedForOp([
                              id |-> Cardinality(operations) + 1,
                              type |-> "delete",
                              principal |-> principal,
                              resource |-> resource,
                              node |-> node,
                              timestamp |-> CHOOSE t \in 0..MaxOperations : TRUE,
                              status |-> "pending"
                           ])
                           THEN "authorized" ELSE "denied"
         ]
       IN /\ operations' = operations \union {newOp}
          /\ signatures' =
               IF newOp.status = "authorized" /\ newOp.id <= MaxOperations
               THEN [signatures EXCEPT ![newOp.id] = Hash(newOp)]
               ELSE signatures
    /\ UNCHANGED <<policies, delegations>>

Next ==
    \/ \E p \in Principals, r \in Resources, n \in Nodes : CreateOperation(p, r, n)
    \/ \E p \in Principals, r \in Resources, n \in Nodes : ModifyOperation(p, r, n)
    \/ \E p \in Principals, r \in Resources, n \in Nodes : DeleteOperation(p, r, n)
    \/ \E d, g \in Principals, r \in Resources, perms \in SUBSET Alphabet : AddDelegation(d, g, r, perms)

StateConstraint ==
    /\ Cardinality(operations) <= 2
    /\ Cardinality(delegations) <= 1
    /\ TLCGet("level") <= 5


Spec == Init /\ [][Next]_<<operations, policies, delegations, signatures>>

====

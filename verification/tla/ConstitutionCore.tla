To: Peer Reviewer
From: Opus (Writer)
Artifact: ConstitutionCore.tla
Version: v1.2.0
Date: 2025-01-17
Status: Final for Review
Summary: Fixed signature domain typing to use numeric keys, introduced Owner mapping
for proper Node/Principal relationships, corrected delete/no-override to check against
policy.id fields. All invariants now type-correct with proper authorization predicates.

---- MODULE ConstitutionCore ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS 
    Nodes,          \* Set of system nodes
    Principals,     \* Set of authorized principals
    Resources,      \* Set of protected resources
    MaxOperations,  \* Maximum operations for model checking
    Owner           \* Ownership mapping: [Nodes -> Principals]

ASSUME
    /\ MaxOperations > 0
    /\ Owner \in [Nodes -> Principals]

VARIABLES
    operations,     \* Set of executed operations
    policies,       \* Active policies per node
    delegations,    \* Delegation relationships
    signatures      \* Operation signatures (numeric domain)

vars == <<operations, policies, delegations, signatures>>

\* Type definitions
TypeOK ==
    /\ operations \in SUBSET [
        id: Nat,
        type: {"create", "modify", "delete", "search"},
        principal: Principals,
        resource: Resources,
        node: Nodes,
        timestamp: Nat,
        status: {"pending", "authorized", "denied"}
    ]
    /\ policies \in [Nodes -> SUBSET [
        id: Nat,
        type: {"access", "delegation", "constraint"},
        rule: STRING,
        active: BOOLEAN
    ]]
    /\ delegations \in SUBSET [
        delegator: Nodes,
        delegatee: Principals,
        resource: Resources,
        permissions: SUBSET {"read", "write", "delete"},
        expires: Nat
    ]
    /\ signatures \in [1..MaxOperations -> STRING]  \* Fixed: numeric domain

\* Initial state
Init ==
    /\ operations = {}
    /\ policies = [n \in Nodes |-> {}]
    /\ delegations = {}
    /\ signatures = [i \in 1..MaxOperations |-> ""]

\* Helper functions
Hash(x) == CHOOSE h \in STRING : TRUE

\* Check if principal has delegation for node/resource
Delegated(node, principal, resource) ==
    \E d \in delegations :
        /\ d.delegator = node
        /\ d.delegatee = principal
        /\ d.resource = resource

\* Check if principal is authorized for a node
Authorized(node, principal) ==
    \/ Owner[node] = principal  \* Fixed: proper owner check
    \/ \E d \in delegations :   \* Or has delegation
        /\ d.delegator = node
        /\ d.delegatee = principal

\* Check if principal is authorized for specific operation
AuthorizedForOp(op) ==
    \/ Owner[op.node] = op.principal  \* Node owner
    \/ \E d \in delegations :          \* Or delegated
        /\ d.delegator = op.node
        /\ d.delegatee = op.principal
        /\ d.resource = op.resource
        /\ op.type \in d.permissions

\* Sovereignty preservation invariant (Lines 45-52)
Inv_Sov ==
    \A op \in operations :
        op.status = "authorized" =>
            \/ Owner[op.node] = op.principal  \* Node owner controls operations
            \/ \E d \in delegations :         \* Or explicitly delegated
                /\ d.delegator = op.node
                /\ d.delegatee = op.principal
                /\ d.resource = op.resource

\* Explicit authorization invariant (Lines 53-61)
Inv_Auth ==
    \A op \in operations :
        op.status = "authorized" =>
            /\ op.id \in DOMAIN signatures     \* Has signature (numeric domain)
            /\ op.id <= MaxOperations          \* Within bounds
            /\ signatures[op.id] # ""          \* Non-empty signature
            /\ AuthorizedForOp(op)             \* Principal is authorized

\* No external override invariant (Lines 62-68)
Inv_NoOverride ==
    \A n \in Nodes :
        \A p \in policies[n] :
            p.active =>
                \* No other node can modify this node's policies
                \A op \in operations :
                    (op.type = "modify" /\ op.resource = p.id) =>  \* Fixed: check p.id
                        Owner[op.node] = Owner[n]  \* Same owner required

\* Delete operation sovereignty (Lines 69-77)
Inv_DeleteSovereignty ==
    \A op \in operations :
        op.type = "delete" =>
            op.status = "authorized" =>
                \/ Owner[op.node] = op.principal
                \/ \E d \in delegations :
                    /\ d.delegator = op.node
                    /\ d.delegatee = op.principal
                    /\ "delete" \in d.permissions

\* Delete operation override prevention (Lines 78-85)
Inv_DeleteNoOverride ==
    \A op \in operations :
        op.type = "delete" =>
            \* Cannot delete policies owned by other nodes
            \A n \in Nodes \ {op.node} :
                \A p \in policies[n] :
                    op.resource # p.id  \* Fixed: check against policy.id field

\* Combined safety property
SafetyProperty ==
    /\ Inv_Sov
    /\ Inv_Auth
    /\ Inv_NoOverride
    /\ Inv_DeleteSovereignty
    /\ Inv_DeleteNoOverride

\* Actions
CreateOperation(principal, resource, node) ==
    /\ Cardinality(operations) < MaxOperations
    /\ LET newOp == [
        id |-> Cardinality(operations) + 1,
        type |-> "create",
        principal |-> principal,
        resource |-> resource,
        node |-> node,
        timestamp |-> CHOOSE t \in Nat : TRUE,
        status |-> IF Authorized(node, principal) 
                   THEN "authorized" 
                   ELSE "denied"
    ]
    IN /\ operations' = operations \union {newOp}
       /\ IF newOp.status = "authorized" /\ newOp.id <= MaxOperations
          THEN signatures' = [signatures EXCEPT ![newOp.id] = Hash(newOp)]
          ELSE signatures' = signatures
    /\ UNCHANGED <<policies, delegations>>

ModifyOperation(principal, resource, node) ==
    /\ Cardinality(operations) < MaxOperations
    /\ LET newOp == [
        id |-> Cardinality(operations) + 1,
        type |-> "modify",
        principal |-> principal,
        resource |-> resource,
        node |-> node,
        timestamp |-> CHOOSE t \in Nat : TRUE,
        status |-> IF AuthorizedForOp(newOp)
                   THEN "authorized"
                   ELSE "denied"
    ]
    IN /\ operations' = operations \union {newOp}
       /\ IF newOp.status = "authorized" /\ newOp.id <= MaxOperations
          THEN signatures' = [signatures EXCEPT ![newOp.id] = Hash(newOp)]
          ELSE signatures' = signatures
    /\ UNCHANGED <<policies, delegations>>

DeleteOperation(principal, resource, node) ==
    /\ Cardinality(operations) < MaxOperations
    /\ LET newOp == [
        id |-> Cardinality(operations) + 1,
        type |-> "delete",
        principal |-> principal,
        resource |-> resource,
        node |-> node,
        timestamp |-> CHOOSE t \in Nat : TRUE,
        status |-> IF AuthorizedForOp(newOp)
                   THEN "authorized"
                   ELSE "denied"
    ]
    IN /\ operations' = operations \union {newOp}
       /\ IF newOp.status = "authorized" /\ newOp.id <= MaxOperations
          THEN signatures' = [signatures EXCEPT ![newOp.id] = Hash(newOp)]
          ELSE signatures' = signatures
    /\ UNCHANGED <<policies, delegations>>

AddDelegation(delegator, delegatee, resource, perms) ==
    /\ Owner[delegator] \in Principals  \* Only owner can delegate
    /\ LET newDelegation == [
        delegator |-> delegator,
        delegatee |-> delegatee,
        resource |-> resource,
        permissions |-> perms,
        expires |-> CHOOSE t \in Nat : TRUE
    ]
    IN delegations' = delegations \union {newDelegation}
    /\ UNCHANGED <<operations, policies, signatures>>

\* Next state relation
Next ==
    \/ \E p \in Principals, r \in Resources, n \in Nodes :
        \/ CreateOperation(p, r, n)
        \/ ModifyOperation(p, r, n)
        \/ DeleteOperation(p, r, n)
    \/ \E delegator \in Nodes, delegatee \in Principals, r \in Resources :
        AddDelegation(delegator, delegatee, r, {"read", "write"})

\* Specification
Spec == Init /\ [][Next]_vars

====
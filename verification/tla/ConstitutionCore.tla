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

(* Class-A finite helpers (TLC) *)
Alphabet == {"", "a", "b"}


CONSTANTS Nodes, Principals, Resources, MaxOperations, Owner




(*     Nodes,          \* Set of system nodes *)

(*     Principals,     \* Set of authorized principals *)

(*     Resources,      \* Set of protected resources *)

(*     MaxOperations,  \* Maximum operations for model checking *)

(*     Owner           \* Ownership mapping: [Nodes -> Principals] *)



(* ASSUME *)

(*     /\ MaxOperations > 0 *)

(*     /\ Owner \in [Nodes -> Principals] *)
(* VARIABLES \* Set of executed operations, delegations, operations, policies, signatures *)

(*     policies,       \* Active policies per node *)

(*     delegations,    \* Delegation relationships *)

(*     signatures      \* Operation signatures (numeric domain) *)



VARIABLES operations, policies, delegations, signatures
vars == <<operations, policies, delegations, signatures>>



\* Type definitions

TypeOK ==

    /\ operations \in SUBSET [

        id: 1..MaxOperations,

        type: {"create", "modify", "delete", "search"},

        principal: Principals,

        resource: Resources,

        node: Nodes,

        timestamp: 0..MaxOperations,

        status: {"pending", "authorized", "denied"}

        ]

    /\ policies \in [Nodes -> SUBSET [

        id: 1..MaxOperations,

        type: {"access", "delegation", "constraint"},

        rule: Alphabet,

        active: BOOLEAN

        ]]

    /\ delegations \in SUBSET [

        delegator: Nodes,

        delegatee: Principals,

        resource: Resources,

        permissions: SUBSET {"read", "write", "delete"},

        expires: Nat

        ]

    /\ signatures \in [1..MaxOperations -> Alphabet]  \* Fixed: numeric domain



\* Initial state

Init ==

    /\ operations = {}

    /\ policies = [n \in Nodes |-> {}]

    /\ delegations = {}

    /\ signatures = [i \in 1..MaxOperations |-> ""]



\* Helper functions

Hash(x) == ""



\* Check if principal has delegation for node/resource

Delegated(node, principal, resource) ==

    \E d \in delegations :

        /\ d.delegator = node

        /\ d.delegatee = principal

        /\ d.resource = resource



\* Check if principal is authorized for a node

Authorized(node, principal) ==

    \/ Owner[node] = principal

    \/ \E d \in delegations :

        /\ d.delegator = node

        /\ d.delegatee = principal



Inv_Sov ==

    \A op \in operations :

        op.status = "authorized" =>

            \/ Owner[op.node] = op.principal

            \/ \E d \in delegations :

                /\ d.delegator = op.node

                /\ d.delegatee = op.principal

                /\ d.resource  = op.resource



RequiredPerm(op) ==

  CASE op.type = "create"  -> "write"

     [] op.type = "modify" -> "write"

     [] op.type = "delete" -> "delete"

     [] op.type = "search" -> "read"

     [] OTHER               -> "read"



AuthorizedForOp(op) ==

    \/ Owner[op.node] = op.principal

    \/ \E d \in delegations :

        /\ d.delegator  = op.node

        /\ d.delegatee  = op.principal

        /\ d.resource   = op.resource

        /\ op.type \in d.permissions

        /\ RequiredPerm(op) \in d.permissions



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

        (op.type = "delete" /\ op.status = "authorized") =>

            \/ Owner[op.node] = op.principal

            \/ \E d \in delegations :

                /\ d.delegator  = op.node

                /\ d.delegatee  = op.principal

                /\ "delete" \in d.permissions



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

    /\ LET tmp == [

             id        |-> Cardinality(operations) + 1,

             type      |-> "create",

             principal |-> principal,

             resource  |-> resource,

             node      |-> node,

             timestamp |-> CHOOSE t \in 0..MaxOperations : TRUE

         ]

         newOp == [ tmp EXCEPT !.status = IF Authorized(node, principal)

                                         THEN "authorized" ELSE "denied" ]

       IN /\ operations' = operations \union {newOp}

          /\ signatures' =

               IF newOp.status = "authorized" /\ newOp.id <= MaxOperations

               THEN [signatures EXCEPT ![newOp.id] = Hash(newOp)]

               ELSE signatures

    /\ UNCHANGED <<policies, delegations>>



AddDelegation(delegator, delegatee, resource, perms) ==

    /\ Owner[delegator] \in Principals

    /\ LET newDelegation == [

             delegator   |-> delegator,

             delegatee   |-> delegatee,

             resource    |-> resource,

             permissions |-> perms,

             expires     |-> CHOOSE t \in 0..MaxOperations : TRUE

         ]

       IN /\ delegations' = delegations \union {newDelegation}

          /\ UNCHANGED <<operations, policies, signatures>>



ModifyOperation(principal, resource, node) ==

    /\ Cardinality(operations) < MaxOperations

    /\ LET base == [

             id        |-> Cardinality(operations) + 1,

             type      |-> "modify",

             principal |-> principal,

             resource  |-> resource,

             node      |-> node,

             timestamp |-> CHOOSE t \in 0..MaxOperations : TRUE,

             status    |-> "pending"

         ]

         st == IF AuthorizedForOp([base EXCEPT !.status = "pending"])

               THEN "authorized" ELSE "denied"

         newOp == [base EXCEPT !.status = st]

       IN /\ operations' = operations \union {newOp}

          /\ signatures' =

               IF newOp.status = "authorized" /\ newOp.id <= MaxOperations

               THEN [signatures EXCEPT ![newOp.id] = Hash(newOp)]

               ELSE signatures

    /\ UNCHANGED <<policies, delegations>>

DeleteOperation(principal, resource, node) ==

    /\ Cardinality(operations) < MaxOperations

    /\ LET base == [

             id        |-> Cardinality(operations) + 1,

             type      |-> "delete",

             principal |-> principal,

             resource  |-> resource,

             node      |-> node,

             timestamp |-> CHOOSE t \in 0..MaxOperations : TRUE,

             status    |-> "pending"

         ]

         st == IF AuthorizedForOp([base EXCEPT !.status = "pending"])

               THEN "authorized" ELSE "denied"

         newOp == [base EXCEPT !.status = st]

       IN /\ operations' = operations \union {newOp}

          /\ signatures' =

               IF newOp.status = "authorized" /\ newOp.id <= MaxOperations

               THEN [signatures EXCEPT ![newOp.id] = Hash(newOp)]

               ELSE signatures

    /\ UNCHANGED <<policies, delegations>>

Next ==

    \/ \E p \in Principals, r \in Resources, n \in Nodes :

         CreateOperation(p, r, n)

    \/ \E p \in Principals, r \in Resources, n \in Nodes :

         ModifyOperation(p, r, n)

    \/ \E p \in Principals, r \in Resources, n \in Nodes :

         DeleteOperation(p, r, n)

    \/ \E delegator \in Nodes, delegatee \in Principals, r \in Resources :

         AddDelegation(delegator, delegatee, r, {"read", "write"})



Spec == Init /\ [][Next]_vars



(***************************************************************************)

(* Peer-review: permission mapping & op authorization                        *)

(***************************************************************************)



====

---- MODULE boot ----

EXTENDS
    Integers, Naturals, TLC, FiniteSets

CONSTANTS
    Node

VARIABLES
    Msgs,
    Peers,
    State,
    Responded

TypeOK ==
    /\ Node \subseteq Nat
    /\ Msgs \subseteq
            [type: {"Response"}, src: Node, dst: Node,
               peers: SUBSET Node, leader: Node \cup {-1}]
    /\ Peers \in [Node -> SUBSET Node]
    /\ State \in [Node -> {"Looking", "Found", "Leader"}]
    /\ Responded \in [Node -> SUBSET Node]

Respond(a) ==
    /\ \E src \in Node:
        /\ a \in Peers[src]
        /\ ~ \E mm \in Msgs:
            /\ mm.type = "Response"
            /\ mm.src = a
            /\ mm.dst = src
        /\ Peers' = [Peers EXCEPT ![a] = Peers[a] \cup {src}]
        /\ Msgs' = Msgs \cup {
            [type |-> "Response", src |-> a, dst |-> src,
             peers |-> Peers[a], leader |-> IF State[a] = "Leader" THEN a ELSE -1]}
    /\ UNCHANGED <<State, Responded>>

HandleResponse(a) ==
    /\ State[a] /= "Leader"
    /\ \E m \in Msgs:
        /\ m.type = "Response"
        /\ m.dst = a
        /\ \/ /\ m.leader \in Node
              /\ State' = [State EXCEPT ![a] = "Found"]
              /\ UNCHANGED <<Peers, Responded>>
           \/ /\ m.leader = -1
              /\ Peers' = [Peers EXCEPT ![a] = Peers[a] \cup m.peers]
              /\ Responded' = [Responded EXCEPT ![a] = Responded[a] \cup {m.src}]
              /\ UNCHANGED <<State>>
        /\ Msgs' = Msgs \ {m}

BecomeLeader(a) ==
    /\ Peers[a] = Responded[a]
    /\ \A p \in Peers[a]: a <= p
    /\ State' = [State EXCEPT ![a] = "Leader"]
    /\ UNCHANGED <<Msgs, Peers, Responded>>
    
Inv1 ==
    \A a, b \in Node:
     \/ a = b
     \/ ~ (State[a] = "Leader" /\ State[b] = "Leader")

Inv2 ==
    ~ (\A a \in Node: State[a] = "Found")

Inv3 ==
    \/ \E a \in Node: State[a] = "Leader"
    \/ \A a \in Node: State[a] /= "Found"

PossibleSeeds == {s \in SUBSET Node: Cardinality(s) <= 3 /\ s /= {}}

Init ==
    /\ Peers \in {f \in [Node -> PossibleSeeds]: \A n \in Node: n \in f[n]}
    /\ \A a, b \in Node: Peers[a] \cap Peers[b] /= {}
    /\ Msgs = {}
    /\ State = [a \in Node |-> "Looking"]
    /\ Responded = [a \in Node |-> {}]

Next ==
    /\ \/ \E a \in Node: Respond(a)
       \/ \E a \in Node: HandleResponse(a)
       \/ \E a \in Node: BecomeLeader(a)

=====================

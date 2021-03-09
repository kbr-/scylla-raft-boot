---- MODULE boot ----

EXTENDS
    Integers, Naturals, TLC

CONSTANTS
    Node
\*    Seeds

VARIABLES
    Seeds,
    Msgs,
    Peers,
    State,
    Responded,
    Sent

TypeOK ==
    /\ Node \subseteq Nat
    /\ Seeds \in [Node -> SUBSET Node]
    /\ Msgs \subseteq
         [type: {"Request"}, src: Node, dst: Node, peers: SUBSET Node]
            \cup [type: {"Response"}, src: Node, dst: Node,
                    peers: SUBSET Node, leader: Node \cup {-1}]
    /\ Peers \in [Node -> SUBSET Node]
    /\ State \in [Node -> {"Looking", "Found", "Leader"}]
    /\ Responded \in [Node -> SUBSET Node]
    /\ Sent \in [Node -> SUBSET Node]

NewRound(a) ==
    /\ Responded[a] = Sent[a]
    /\ Peers[a] /= Responded[a]
    /\ Sent' = [Sent EXCEPT ![a] = Peers[a]]
    /\ Msgs' = Msgs \cup {[type |-> "Request", src |-> a, dst |-> b, peers |-> Peers[a]]: b \in Peers[a]}
    /\ Responded' = [Responded EXCEPT ![a] = {}]
    /\ UNCHANGED <<Peers, State>>

\* This node should also extend peers?
Respond(a) ==
    /\ \E m \in Msgs:
        /\ m.type = "Request"
        /\ m.dst = a
        /\ Peers' = [Peers EXCEPT ![a] = Peers[a] \cup m.peers]
        /\ Msgs' = Msgs \cup {
            [type |-> "Response", src |-> a, dst |-> m.src,
             peers |-> Peers[a], leader |-> IF State[a] = "Leader" THEN a ELSE -1]}
    /\ UNCHANGED <<Sent, State, Responded>>

HandleResponse(a) ==
    /\ State[a] /= "Leader"
    /\ \E m \in Msgs:
        /\ m.type = "Response"
        /\ m.dst = a
        /\ \/ /\ m.leader \in Node
              /\ State' = [State EXCEPT ![a] = "Found"]
              /\ UNCHANGED <<Peers, Responded, Sent>>
           \/ /\ m.leader = -1
              /\ Peers' = [Peers EXCEPT ![a] = Peers[a] \cup m.peers]
              /\ Responded' = [Responded EXCEPT ![a] = Responded[a] \cup {m.src}]
              /\ UNCHANGED <<State, Sent>>
    /\ UNCHANGED <<Msgs>>

BecomeLeader(a) ==
    /\ Responded[a] = Sent[a]
    /\ Peers[a] = Responded[a]
    /\ \A p \in Peers[a]: a <= p
    /\ State' = [State EXCEPT ![a] = "Leader"]
    /\ UNCHANGED <<Msgs, Peers, Responded, Sent>>
    
Inv1 ==
    \A a, b \in Node:
     \/ a = b
     \/ ~ (State[a] = "Leader" /\ State[b] = "Leader")

Inv2 ==
    ~ (\A a \in Node: State[a] = "Found")

Inv3 ==
    \/ \E a \in Node: State[a] = "Leader"
    \/ \A a \in Node: State[a] /= "Found"

Init ==
    /\ Seeds \in [Node -> ((SUBSET Node) \ {{}})]
    /\ \A a, b \in Node: Seeds[a] \cap Seeds[b] /= {}
    /\ Msgs = {}
    /\ Peers = [a \in Node |-> Seeds[a] \cup {a}]
    /\ State = [a \in Node |-> "Looking"]
    /\ Responded = [a \in Node |-> {}]
    /\ Sent = [a \in Node |-> {}]

Next ==
    /\ \/ \E a \in Node: Respond(a)
       \/ \E a \in Node: HandleResponse(a)
       \/ \E a \in Node: NewRound(a)
       \/ \E a \in Node: BecomeLeader(a)
    /\ UNCHANGED <<Seeds>>

=====================

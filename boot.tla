---- MODULE boot ----

EXTENDS
    Integers, Naturals, TLC, FiniteSets

CONSTANTS
    Node

VARIABLES
    SharedPeers,
    Peers,
    Leader,
    LearnedFrom

TypeOK ==
    /\ Node \subseteq Nat
    /\ SharedPeers \in [Node -> SUBSET [peers: SUBSET Node, leader: Node \cup {-1}]]
    /\ Peers \in [Node -> SUBSET Node]
    /\ Leader \in [Node -> Node \cup {-1}]
    /\ LearnedFrom \in [Node -> SUBSET Node]

SharePeers(a) ==
    /\ \E src \in Node:
        /\ \E sp \in SharedPeers[src]:
            /\ a \in sp.peers
            /\ LearnedFrom' = [LearnedFrom EXCEPT ![a] = LearnedFrom[a] \cup {src}]
            /\ Peers' = [Peers EXCEPT ![a] = Peers[a] \cup sp.peers]
            /\ Leader' = [Leader EXCEPT ![a] = IF sp.leader = -1 THEN Leader[a] ELSE sp.leader]
            /\ SharedPeers' = [SharedPeers EXCEPT ![a] = SharedPeers[a] \cup {[peers |-> Peers'[a], leader |-> Leader'[a]]}]

BecomeLeader(a) ==
    /\ Peers[a] = LearnedFrom[a]
    /\ \A p \in Peers[a]: a <= p
    /\ Leader[a] = -1
    /\ Leader' = [Leader EXCEPT ![a] = a]
    /\ UNCHANGED <<SharedPeers, Peers, LearnedFrom>>
    
Inv1 ==
    \A a, b \in Node:
        \/ Leader[a] = -1
        \/ Leader[b] = -1
        \/ Leader[a] = Leader[b]

Inv2 ==
    \A a \in Node:
        /\ Peers[a] \in {sp.peers: sp \in SharedPeers[a]}
        /\ LearnedFrom[a] \subseteq Peers[a]

G1(a, b, c) == (c :> {c, b}) @@ (b :> {b, a}) @@ (a :> {a})
G2(a, b, c) == (c :> {c, a}) @@ (b :> {b, a}) @@ (a :> {a})
GBad == 0 :> {0,1,2} @@ 1:>{1}@@2:>{2}
G3(a, b, c, d) == G1(a,b,c) @@ (d :> {d, a})
G4(a, b, c, d) == G1(a,b,c) @@ (d :> {d, b})
G5(a, b, c, d) == G1(a,b,c) @@ (d :> {d, c})
G6(a, b, c, d) == G2(a,b,c) @@ (d :> {d, a})

Graphs3(a, b, c) == {G1(a, b, c), G2(a, b, c)}
Graphs4(a, b, c, d) == {G3(a,b,c,d), G4(a,b,c,d), G5(a,b,c,d), G6(a,b,c,d)}

AllGraphs3 == UNION {Graphs3(p[0],p[1],p[2]): p \in Permutations({0,1,2})}
AllGraphs4 == UNION {Graphs4(p[0],p[1],p[2],p[3]): p \in Permutations({0,1,2,3})}

Init ==
    /\ Peers \in AllGraphs4
    /\ Leader = [a \in Node |-> -1]
    /\ SharedPeers = [a \in Node |-> {[peers |-> Peers[a], leader |-> -1]}]
    /\ LearnedFrom = [a \in Node |-> {a}]

Next ==
    /\ \/ \E a \in Node: SharePeers(a)
       \/ \E a \in Node: BecomeLeader(a)

=====================

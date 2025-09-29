---- MODULE bfs ----
EXTENDS TLC, Naturals, FiniteSets, Sequences, Integers

CONSTANT Node

VARIABLES edges
VARIABLES nodes

VARIABLES frontier
VARIABLES visited

VARIABLE startNode

\* Sample graph.
V1 == {1,2,3,4}
E1 == {<<1,2>>, <<1,3>>, <<2,4>>, <<3,4>>}


SeqOf(set, n) == UNION {[1..m -> set] : m \in 0..n}

SimplePath(V, E) ==
    \* A simple path is a path with no repeated nodes.
    {p \in SeqOf(V, Cardinality(V)) :
             /\ p # << >>
             /\ Cardinality({ p[i] : i \in DOMAIN p }) = Len(p)
             /\ \A i \in 1..(Len(p)-1) : <<p[i], p[i+1]>> \in E}

SimplePathsFrom(V, E, start, target) ==
    {p \in SimplePath(V, E) : p[1] = start /\ p[Len(p)] = target}

ShortestPath(start, target) == 
    IF SimplePathsFrom(nodes, edges, start, target) # {} THEN
        Len(CHOOSE p \in SimplePathsFrom(nodes, edges, start, target) : 
                \A p1 \in SimplePathsFrom(nodes, edges, start, target) : Len(p) <= Len(p1)) - 1
    ELSE -1
    

Init == 
    /\ nodes = Node
    /\ edges \in SUBSET (nodes \X nodes)
    /\ startNode \in nodes
    /\ visited = {}
    \* Choose some node as the initial frontier/source.
    /\ frontier = {<<startNode,0>>}

Neighbors(n) == {x \in nodes : <<n,x>> \in edges}

Explore(n) == 
    /\ n \notin visited
    /\ ~\E x \in frontier : x[1] = n
    /\ visited' = visited \cup {n[1]}
    /\  LET newNeighbors == {x \in Neighbors(n[1]) : x \notin visited'} IN
        frontier' = (frontier \ {n}) \cup {<<b, n[2]+1>> : b \in newNeighbors}
    /\ UNCHANGED <<nodes, edges, startNode>>    

Terminate ==
    /\ frontier = {}
    /\ visited = nodes
    /\ UNCHANGED <<nodes, edges, visited, frontier, startNode>>

Next ==
    \/ \E n \in frontier : Explore(n)
    \/ Terminate

Symmetry == Permutations(Node)

L == ~(visited = Node)





====
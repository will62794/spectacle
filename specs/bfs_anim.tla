---- MODULE bfs_anim ----
EXTENDS TLC, SVG, Functions, bfs

DiGraph(V, E, nodeAttrsFn, edgeAttrsFn) == SVGElem("digraph", [V |-> V, E |-> E, nodeAttrsFn |-> nodeAttrsFn, edgeAttrsFn |-> edgeAttrsFn], <<>>, "")

\* Establish a fixed mapping to assign an ordering to elements in these sets.
\* ServerId == CHOOSE f \in [Server -> 1..Cardinality(Person)] : Injective(f)
\* RMId == CHOOSE f \in [1..Cardinality(Server) -> Server] : Injective(f)
\* SetToSeq(S) == CHOOSE f \in [1..Cardinality(S) -> S] : Injective(f)
\* RMId == SetToSeq(Server)
\* CHOOSE f \in [1..Cardinality(Server) -> Server] : Injective(f)

\* Graphviz attributes
nodeAttrsFn(n) == [
    label |-> IF n \in visited THEN ToString(n) ELSE ToString(n), 
    style |-> "filled", 
    fillcolor |-> 
        IF n \in visited THEN "lightblue" 
        ELSE IF \E v \in frontier : v[1] = n THEN "lightgray"
        ELSE "white"
]
edgeAttrsFn(e) == [
    label |-> "",
    color |-> "black"
]
AnimView == Group(<<DiGraph(nodes,edges,[n \in Node |-> nodeAttrsFn(n)], [e \in edges |-> edgeAttrsFn(e)])>>, [i \in {} |-> {}])


\* Animation alias for generating SVG files with TLC
AnimAlias ==
    [
        edges |-> edges,
        nodes |-> nodes,
        frontier |-> frontier,
        visited |-> visited,
        startNode |-> startNode
    ] @@
    [ _anim |-> SVGSerialize(SVGDoc(AnimView, 0, 0, 1000, 1000, <<>>), "bfs_anim_", TLCGet("level")) ]

====

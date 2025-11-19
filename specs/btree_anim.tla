---- MODULE btree_anim ----
EXTENDS SVG, btree

DiGraph(V, E, nodeAttrsFn, edgeAttrsFn) == SVGElem("digraph", [V |-> V, E |-> E, nodeAttrsFn |-> nodeAttrsFn, edgeAttrsFn |-> edgeAttrsFn], <<>>, "")


\* Utility function for a consistent position for nodes in the SVG
\* \* SetToSeq(S) == CHOOSE f \in [1..Cardinality(S) -> S] : Injective(f)

\* \* Returns a nice string label for a node, showing its keys and possibly values
\* NodeLabel(n) == ToString(n)

\* \* Helper: node attributes for Graphviz nodes
\* nodeAttrsFn(n) ==
\*     [
\*         label |-> NodeLabel(n),
\*         style |-> "filled",
\*         fillcolor |-> IF isLeaf[n] THEN "#EFFFEB" ELSE "#D6F0FC",
\*         color |-> IF focus = n THEN "red" ELSE "black",
\*         fontcolor |-> "black",
\*         shape |-> "rect",
\*         width |-> "1",
\*         height |-> "0.7",
\*         penwidth |-> IF focus = n THEN "2" ELSE "1"
\*     ]

\* \* Helper: edge attributes for Graphviz edges
\* edgeAttrsFn(e) ==
\*     [
\*         label |-> e[3],
\*         color |-> "#888",
\*         penwidth |-> "2",
\*         fontcolor |-> "#444",
\*         fontsize |-> "10"
\*     ]

\* \* Node set
\* graphNodes == { n \in Nodes : keysOf[n] # {} }

\* \* Edge set: (parent, child, label) triples for dot
graphEdges == {e \in DOMAIN childOf : childOf[e] # "none"}

\* DiGraph view (Graphviz-compatible via SVG extension)
\* Nodes == {"a","b"}
\* Edges == {<<"a","b">>}
AnimView ==
    Group(<<DiGraph(
        Nodes,
        graphEdges,
        [n \in Nodes |-> [
            label |-> ToString(n), 
            fillcolor |-> IF n = root THEN "lightgray" ELSE "none", 
            style |-> "filled",
            color |-> IF n = focus THEN "green" ELSE "black",
            penwidth |-> IF n = focus THEN "3" ELSE "1",
            shape |-> "rect"
            ]],
        [e \in graphEdges |-> [label |-> ""]]
    )>>, [i \in {} |-> {}])


\* AnimView ==
\*     Group(<<Circle(10, 10, 10, [fill |-> "red"])>>, [i \in {} |-> {}])




====
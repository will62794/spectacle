---- MODULE gfd_anim ----
EXTENDS TLC, Sequences, gfd



\* Merge two records
MergeFn(r1, r2) == 
    LET D1 == DOMAIN r1 D2 == DOMAIN r2 IN
    [k \in (D1 \cup D2) |-> IF k \in D1 THEN r1[k] ELSE r2[k]]

SVGElem(_name, _attrs, _children, _innerText) == [name |-> _name, attrs |-> _attrs, children |-> _children, innerText |-> _innerText ]

Text(x, y, text, attrs) == 
    (**************************************************************************)
    (* Text element.'x' and 'y' should be given as integers, and 'text' given *)
    (* as a string.                                                           *)
    (**************************************************************************)
    LET svgAttrs == [x |-> x, 
                     y |-> y] IN
    SVGElem("text", MergeFn(svgAttrs, attrs), <<>>, text) 

\* Circle element. 'cx', 'cy', and 'r' should be given as integers.
Circle(cx, cy, r, attrs) == 
    LET svgAttrs == [cx |-> cx, 
                     cy |-> cy, 
                     r  |-> r] IN
    SVGElem("circle", MergeFn(svgAttrs, attrs), <<>>, "")

\* Rectangle element. 'x', 'y', 'w', and 'h' should be given as integers.
Rect(x, y, w, h, attrs) == 
    LET svgAttrs == [x      |-> x, 
                     y      |-> y, 
                     width  |-> w, 
                     height |-> h] IN
    SVGElem("rect", MergeFn(svgAttrs, attrs), <<>>, "")

Image(x, y, width, height, href, attrs) == 
    LET svgAttrs == ("xlink:href" :> href @@
                     "x"         :> x @@
                     "y"         :> y @@
                     "width"     :> width @@
                     "height"    :> height) IN
    SVGElem("image", MergeFn(svgAttrs, attrs), <<>>, "")

\* Group element. 'children' is as a sequence of elements that will be contained in this group.
Group(children, attrs) == SVGElem("g", attrs, children, "")

\* Edges can also be specified as tuples of length > 2, such as <<n1,n2,x,y,z>>,
\* which defines an edge between n1 -> n2, but x,y,z define additional metadata
\* specific to that edge e.g. this also allows for multiple edges between the
\* same nodes in the same direction, but with potentially different edge
\* "types".
DiGraph(V, E, nodeAttrsFn, edgeAttrsFn, graphAttrs) == SVGElem("digraph", [V |-> V, E |-> E, nodeAttrsFn |-> nodeAttrsFn, edgeAttrsFn |-> edgeAttrsFn, graphAttrs |-> graphAttrs], <<>>, "")

Injective(f) == \A x, y \in DOMAIN f : f[x] = f[y] => x = y

GetCommit(cid) == CHOOSE x \in {cm \in commits : cm.commitId = cid} : TRUE

GraphvizHtml(s) == "< <FONT POINT-SIZE=38.0>" \o s \o "</FONT> >"


\* Graphviz attributes
nodeAttrsFn(n) == [
    label |->  ToString(n) \o "\n" \o ToString(GetCommit(n).tables) \o "\n branches:" \o ToString({b \in branches : b = n}),
    shape |-> "rect",
    style |-> "rounded,filled"
]

edgeAttrsFn(e) == [
    label |-> "",
    color |-> "black",
    fontsize |-> "8"
]


commitNodes == {c.commitId : c \in commits}
commitEdges == UNION {{<<p,c.commitId>> : p \in c.parents} : c \in commits}
graphElem == 
    DiGraph(
        commitNodes, 
        commitEdges, 
        [n \in commitNodes |-> nodeAttrsFn(n)], 
        [e \in commitEdges |-> edgeAttrsFn(e)], 
        ("rankdir" :> "LR")
    )

AnimView == Group(<<graphElem>>, [transform |-> "translate(40,40)"])

====
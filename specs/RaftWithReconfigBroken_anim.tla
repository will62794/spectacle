---- MODULE RaftWithReconfigBroken_anim ----
EXTENDS TLC, RaftWithReconfigBroken, Functions, SVG

\* 
\* Animation definition.
\* 

Injective(f) == \A x, y \in DOMAIN f : f[x] = f[y] => x = y

\* Merge two records
Merge(r1, r2) == 
    LET D1 == DOMAIN r1 D2 == DOMAIN r2 IN
    [k \in (D1 \cup D2) |-> IF k \in D1 THEN r1[k] ELSE r2[k]]


Image(x, y, width, height, href, attrs) == 
    LET svgAttrs == ("xlink:href" :> href @@
                     "x"         :> x @@
                     "y"         :> y @@
                     "width"     :> width @@
                     "height"    :> height) IN
    SVGElem("image", Merge(svgAttrs, attrs), <<>>, "")


\* 
\* Define Raft protocol state visualization.
\* 


Spacing == 40

CrownIcon == "assets/crown.svg"
BugIcon == "assets/bug.svg"

CrownElem(xbase, rmid, i) == Image(xbase, i * Spacing - 6, 13, 13, CrownIcon, IF state[rmid] # Leader THEN [hidden |-> "true"] ELSE <<>>)

\* Establish a fixed mapping to assign an ordering to elements in these sets.
\* ServerId == CHOOSE f \in [Server -> 1..Cardinality(Person)] : Injective(f)
SetToSeq(S) == CHOOSE f \in [1..Cardinality(S) -> S] : Injective(f)
RMId == SetToSeq(Server)

\* Animation view definition.
c1 == Circle(10, 10, 5, [fill |-> "red"])
c2 == Circle(20, 10, 5, [fill |-> "red"])
\* ServerIdDomain == 1..Cardinality(Server)
RMIdDomain == 1..Cardinality(Server)
XBase == -15

\* 
\* Define log elements visuals.
\* 

\* Mark if [i][ind] is a *reconfig* log entry: 
\* it is the first entry in log[i] with its config version value.
IsReconfigEntry(i, ind) ==
    LET configVersion == log[i][ind].v IN
      \A j \in 1..(ind-1) : log[i][j].v # configVersion

\* Show committed entries with limegreen border, others with black. No special color for reconfig.
logEntryStyle(i,ind) == 
    IF \E c \in committedEntries : c.index = ind /\ c.term = log[i][ind].term 
        THEN ("fill" :> "lightgray" @@ "stroke" :> "limegreen" @@ "stroke-width" :> "1.5px")
        ELSE ("fill" :> "lightgray" @@ "stroke" :> "black" @@ "stroke-width" :> "1px")

\* Log entry text always just the term.
logEntryText(i, ind) == ToString(log[i][ind].term)

\* If it's a reconfig entry, add a small "RC" label atop the box.
logEntry(i, ybase, ind) == 
    IF IsReconfigEntry(i, ind)
        THEN Group(<<
                Rect(18 * ind + 110, ybase, 16, 16, logEntryStyle(i,ind)),
                Text(18 * ind + 115, ybase - 5, "RC", ("text-anchor" :> "start" @@ "font-size" :> "7px" @@ "font-family" :> "monospace" @@ "fill" :> "blue")),
                Text(18 * ind + 115, ybase + 12, logEntryText(i, ind), ("text-anchor" :> "start" @@ "font-size" :> "10px"))
            >>, [h \in {} |-> {}])
        ELSE Group(<<
                Rect(18 * ind + 110, ybase, 16, 16, logEntryStyle(i,ind)),
                Text(18 * ind + 115, ybase + 12, logEntryText(i, ind), ("text-anchor" :>  "start" @@ "font-size" :> "10px"))
            >>, [h \in {} |-> {}])

logElem(i, ybase) == Group([ind \in DOMAIN log[i] |-> logEntry(i, ybase, ind)], [h \in {} |-> {}])
logElems ==  [i \in RMIdDomain |-> logElem(RMId[i], i * Spacing - 9)]

\* 
\* Define legend for visualization.
\* 
LegendCommittedEntryBox == Rect(22, -3, 13, 13, ("fill" :> "lightgray" @@ "stroke" :> "limegreen" @@ "stroke-width" :> "1.5px"))
LegendCommittedEntryLabel == Text(42, 7, "Committed", ("fill" :> "black" @@ "font-size" :> "8px" @@ "text-anchor" :> "start"))
ConfigLabel == Text(48, 30, "Config", ("fill" :> "gray" @@ "font-size" :> "7px" @@ "text-anchor" :> "start" @@ "text-decoration" :> "underline"))
LegendGroup == Group(<<LegendCommittedEntryBox, LegendCommittedEntryLabel, ConfigLabel>>, [transform |-> "translate(0,0)"])

\* 
\* Define server elements visuals.
\* 
cs == [i \in RMIdDomain |-> 
        Group(<<Circle(XBase + 20, i * Spacing, 10, 
        [stroke |-> "black", fill |-> 
            IF state[RMId[i]] = Leader 
                THEN "gold" 
            ELSE IF state[RMId[i]] = Follower THEN "gray" 
            ELSE IF state[RMId[i]] = Follower THEN "red" ELSE "gray"]),
            CrownElem(XBase-10, RMId[i],i)>>, [h \in {} |-> {}])
        ]

configStr(i) == ToString(ServerViewOn(RMId[i]))
labels == [i \in RMIdDomain |-> Text(XBase + 38, i * Spacing + 5, 
        \* ToString(RMId[i]) \o ", t=" \o ToString(currentTerm[RMId[i]]) \o ",  " \o configStr(i), 
        ToString(RMId[i]) \o "     " \o configStr(i), 
        [fill |-> 
            IF state[RMId[i]] = Leader 
                THEN "black" 
            ELSE IF state[RMId[i]] = Follower THEN "black" 
            ELSE IF state[RMId[i]] = Candidate THEN "red" ELSE "gray"] @@ ("font-family" :> "monospace" @@ "font-size" :> "8px"))] 

termLabels == 
    [i \in RMIdDomain |-> 
        Group(<<Text(XBase + 38 + currentTerm[RMId[i]] * 11, i * Spacing + 20, 
        "" \o ToString(currentTerm[RMId[i]]), 
            [fill |-> 
                IF state[RMId[i]] = Leader 
                    THEN "black" 
                ELSE IF state[RMId[i]] = Follower THEN "black" 
                ELSE IF state[RMId[i]] = Candidate THEN "red" ELSE "gray"] @@ ("font-family" :> "monospace" @@ "font-size" :> "7px")),
        Text(XBase + 10, i * Spacing + 20, 
        "term:", 
            [fill |-> 
                IF state[RMId[i]] = Leader 
                    THEN "black" 
                ELSE IF state[RMId[i]] = Follower THEN "black" 
                ELSE IF state[RMId[i]] = Candidate THEN "red" ELSE "gray"] @@ ("font-family" :> "monospace" @@ "font-size" :> "7px")),
        Rect(XBase + 35, i * Spacing + 20, 100, 1, [fill |-> "white"])
        >>, <<>>)]

\* 
\* Visualize committed safety violation at appropriate index.
\* 

\* Exists a different server with a conflicting committed entry at the same index.
existsConflictingEntry(ind) == \E x,y \in committedEntries : x.index = ind /\ (x.index = y.index) /\ x.term # y.term
violationEntry(ybase, ind) == 
    Group(<<
       Text(16 * ind + 85, ybase - 9, "(StateMachineSafety)", ("fill" :> "red" @@ "font-size" :> "7px" @@ "text-anchor" :> "start")),
       Image(16 * ind + 115, ybase - 6 , 13, 13, BugIcon, <<>>) 
    >>, IF existsConflictingEntry(ind) THEN <<>> ELSE [hidden |-> "true"]) 
violationElem(ybase) == Group([ind \in 1..5 |-> violationEntry(ybase, ind)], <<>>)
violationText == Text(165, 9, "(StateMachineSafety)", (
    "fill" :> "red" @@ "font-size" :> "7px" @@ "text-anchor" :> "start"))
safetyViolationElems ==  <<violationElem(5)>>



\* 
\* Visualizations.
\* 
LogEdges(s) == {<< <<i, log[s][i]>>, <<i+1, log[s][i+1]>> >> : i \in (DOMAIN log[s] \ {Len(log[s])})}
LogTreeEdges == UNION {LogEdges(s) : s \in Server}
LogNodes(s) == {<<i, log[s][i]>> : i \in DOMAIN log[s]}
LogTreeNodes == UNION {LogNodes(s) : s \in Server}

\* Edges can also be specified as tuples of length > 2, such as <<n1,n2,x,y,z>>,
\* which defines an edge between n1 -> n2, but x,y,z define additional metadata
\* specific to that edge e.g. this also allows for multiple edges between the
\* same nodes in the same direction, but with potentially different edge
\* "types".
graphAttrs == ("rankdir" :> "LR")
DiGraph(V, E, nodeAttrsFn, edgeAttrsFn) == SVGElem("digraph", [V |-> V, E |-> E, nodeAttrsFn |-> nodeAttrsFn, edgeAttrsFn |-> edgeAttrsFn, graphAttrs |-> graphAttrs], <<>>, "")


NodeIsServer(n) == \E s \in Server : ToString(s) = n





LogTreeNodeStr(n) == ToString(n[1]) \o "_" \o ToString(n[2])
LogTreeNodesStr == {LogTreeNodeStr(n) : n \in LogTreeNodes}

\* Mapping from log tree node string reprs to their underlying node values.
LogTreeNodeMap == [n \in LogTreeNodesStr |-> CHOOSE x \in LogTreeNodes : LogTreeNodeStr(x) = n]


\* LogTreeNodesStr == {LogTreeNodeStr(n) : n \in LogTreeNodes} \cup {ToString(s) : s \in Server}
LogTreeEdgesStr == {<<LogTreeNodeStr(e[1]), LogTreeNodeStr(e[2])>> : e \in LogTreeEdges}
\* LogTreeEdgesStr == {<<LogTreeNodeStr(e[1]), LogTreeNodeStr(e[2])>> : e \in LogTreeEdges} \cup {<<ToString(s), LogTreeNodeStr(<<Len(log[s]), log[s][Len(log[s])]>>)>> : s \in Server}



\* Graphviz attributes
nodeAttrsFn(n) == 
    LET node == LogTreeNodeMap[n] IN
    [
    label |-> IF NodeIsServer(n) THEN n ELSE "(" \o ToString(node[1]) \o "," \o ToString(node[2].term) \o ")",
    color |-> IF \E c \in committedEntries : c.index = node[1] /\ c.term = node[2].term THEN "green" ELSE "black",
    fillcolor |-> IF NodeIsServer(n) THEN "none" ELSE "white",
    penwidth |-> "2",
    fontsize |-> "12",
    shape |-> "rect", 
    style |-> "rounded,filled"
]

edgeAttrsFn(e) == [
    label |-> "",
    color |-> "black"
    \* fontsize |-> "8"
]

GraphElem == <<Group(<<DiGraph(LogTreeNodesStr,LogTreeEdgesStr,
                                   [n \in LogTreeNodesStr |-> nodeAttrsFn(n)], 
                                   [e \in LogTreeEdgesStr |-> edgeAttrsFn(e)])>>, 
                                   [transform |-> "translate(0, 210) scale(0.67)"])>>


\* 
\* Animation view.
\* 
AnimView == Group(<<LegendGroup>> \o cs \o labels \o termLabels \o logElems \o safetyViolationElems \o GraphElem, [transform |-> "translate(100, 50) scale(1.7)"])



====
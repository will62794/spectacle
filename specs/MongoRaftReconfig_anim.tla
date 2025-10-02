---- MODULE MongoRaftReconfig_anim ----
\*
\* High level specification of Raft protocol with dynamic reconfiguration.
\*

EXTENDS MongoRaftReconfig

\* 
\* Animation stuff.
\* 


\* Merge two records
Merge(r1, r2) == 
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
    SVGElem("text", Merge(svgAttrs, attrs), <<>>, text) 

\* Circle element. 'cx', 'cy', and 'r' should be given as integers.
Circle(cx, cy, r, attrs) == 
    LET svgAttrs == [cx |-> cx, 
                     cy |-> cy, 
                     r  |-> r] IN
    SVGElem("circle", Merge(svgAttrs, attrs), <<>>, "")

\* Group element. 'children' is as a sequence of elements that will be contained in this group.
Group(children, attrs) == SVGElem("g", attrs, children, "")

Injective(f) == \A x, y \in DOMAIN f : f[x] = f[y] => x = y

\* Rectangle element. 'x', 'y', 'w', and 'h' should be given as integers.
Rect(x, y, w, h, attrs) == 
    LET svgAttrs == [x      |-> x, 
                     y      |-> y, 
                     width  |-> w, 
                     height |-> h] IN
    SVGElem("rect", Merge(svgAttrs, attrs), <<>>, "")

Image(x, y, width, height, href, attrs) == 
    LET svgAttrs == ("xlink:href" :> href @@
                     "x"         :> x @@
                     "y"         :> y @@
                     "width"     :> width @@
                     "height"    :> height) IN
    SVGElem("image", Merge(svgAttrs, attrs), <<>>, "")

Spacing == 40

CrownIcon == "assets/crown.svg"
BugIcon == "assets/bug.svg"

CrownElem(xbase, rmid, i) == Image(xbase, i * Spacing - 6, 13, 13, CrownIcon, IF state[rmid] # Primary THEN [hidden |-> "true"] ELSE <<>>)

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
logEntryStyle(i,ind) == 
    IF \E c \in immediatelyCommitted : c[1] = ind /\ c[2] = log[i][ind] 
        THEN ("fill" :> "lightgray" @@ "stroke" :> "limegreen" @@ "stroke-width" :> "1.5px")
        ELSE ("fill" :> "lightgray" @@ "stroke" :> "black" @@ "stroke-width" :> "1px")
logEntry(i, ybase, ind) == Group(<<Rect(18 * ind + 140, ybase, 16, 16, logEntryStyle(i,ind)), 
                                   Text(18 * ind + 145, ybase + 12, ToString(log[i][ind]), ("text-anchor" :>  "start" @@ "font-size" :> "10px"))>>, [h \in {} |-> {}])
logElem(i, ybase) == Group([ind \in DOMAIN log[i] |-> logEntry(i, ybase, ind)], [h \in {} |-> {}])
logElems ==  [i \in RMIdDomain |-> logElem(RMId[i], i * Spacing - 9)]

\* 
\* Define server elements visuals.
\* 
cs == [i \in RMIdDomain |-> 
        Group(<<Circle(XBase + 20, i * Spacing, 10, 
        [stroke |-> "black", fill |-> 
            IF state[RMId[i]] = Primary 
                THEN "gold" 
            ELSE IF state[RMId[i]] = Secondary THEN "gray" 
            ELSE IF state[RMId[i]] = Secondary THEN "red" ELSE "gray"]),
            CrownElem(XBase-10, RMId[i],i)>>, [h \in {} |-> {}])
        ]

configStr(rmid) == ToString(config[rmid])
configVersionAndTermStr(rmid) == "(" \o ToString(configVersion[rmid]) \o ", " \o ToString(configTerm[rmid]) \o ")"
labelText(i, rmid) == 
    Group(<<
        Text(XBase + 38, i * Spacing + 5, 
            ToString(rmid) \o "     " \o configStr(rmid), 
                [fill |-> 
                    IF state[rmid] = Primary 
                        THEN "black" 
                    ELSE IF state[rmid] = Secondary THEN "black" 
                    ELSE "gray"] @@ ("font-family" :> "monospace" @@ "font-size" :> "8px"))
                    ,
        Text(XBase + 130, i * Spacing + 5, configVersionAndTermStr(rmid), ("fill" :> "black" @@ "font-family" :> "monospace" @@ "font-size" :> "6px"))
            >>, [h \in {} |-> {}])

labels == [i \in RMIdDomain |-> labelText(i, RMId[i])] 

configVersionTermTitleLabel == <<Text(100,20, "(version, term)", ("fill" :> "black" @@ "font-family" :> "monospace" @@ "font-size" :> "6px"))>>

termLabels == 
    [i \in RMIdDomain |-> 
        Group(<<Text(XBase + 38 + currentTerm[RMId[i]] * 11, i * Spacing + 20, 
        "" \o ToString(currentTerm[RMId[i]]), 
            [fill |-> 
                IF state[RMId[i]] = Primary 
                    THEN "black" 
                ELSE IF state[RMId[i]] = Secondary THEN "black" 
                ELSE "gray"] @@ ("font-family" :> "monospace" @@ "font-size" :> "7px")),
        Text(XBase + 10, i * Spacing + 20, 
        "term:", 
            [fill |-> 
                IF state[RMId[i]] = Primary 
                    THEN "black" 
                ELSE IF state[RMId[i]] = Secondary THEN "black" 
                ELSE "gray"] @@ ("font-family" :> "monospace" @@ "font-size" :> "7px")),
        Rect(XBase + 35, i * Spacing + 20, 100, 1, [fill |-> "white"])
        >>, <<>>)]

\* 
\* Visualize committed safety violation at appropriate index.
\* 

\* Exists a different server with a conflicting committed entry at the same index.
existsConflictingEntry(ind) == \E x,y \in immediatelyCommitted : x[1] = ind /\ (x[1] = y[1]) /\ x[2] # y[2]
violationEntry(ybase, ind) == Image(16 * ind + 115, ybase + 9, 13, 13, BugIcon, IF existsConflictingEntry(ind) THEN <<>> ELSE [hidden |-> "true"]) 
violationElem(ybase) == Group([ind \in 1..5 |-> violationEntry(ybase, ind)], <<>>)
safetyViolationElems ==  <<violationElem(5)>>


\* 
\* Animation view.
\* 
AnimView == Group(cs \o labels \o termLabels \o logElems \o safetyViolationElems \o configVersionTermTitleLabel, [transform |-> "translate(120, 30) scale(1.75)"])


=============================================================================

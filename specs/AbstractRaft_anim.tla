---- MODULE AbstractRaft_anim ----
\*
\* High level specification of Raft protocol without dynamic reconfiguration.
\*

EXTENDS Naturals, Integers, FiniteSets, Sequences, TLC, AbstractRaft


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

\* Group element. 'children' is as a sequence of elements that will be contained in this group.
Group(children, attrs) == SVGElem("g", attrs, children, "")

Injective(f) == \A x, y \in DOMAIN f : f[x] = f[y] => x = y

\* Establish a fixed mapping to assign an ordering to elements in these sets.
\* ServerId == CHOOSE f \in [Server -> 1..Cardinality(Person)] : Injective(f)
\* RMId == CHOOSE f \in [1..Cardinality(Server) -> Server] : Injective(f)
SetToSeq(S) == CHOOSE f \in [1..Cardinality(S) -> S] : Injective(f)
RMId == SetToSeq(Server)
\* CHOOSE f \in [1..Cardinality(Server) -> Server] : Injective(f)



\* Animation view definition.
c1 == Circle(10, 10, 5, [fill |-> "red"])
c2 == Circle(20, 10, 5, [fill |-> "red"])
\* ServerIdDomain == 1..Cardinality(Server)
RMIdDomain == 1..Cardinality(Server)
Spacing == 40
XBase == 30
logEntryStroke(i,ind) == IF \E c \in committed : c[1] = ind /\ c[2] = log[i][ind] THEN "orange" ELSE "black"
logEntry(i, ybase, ind) == Group(<<Rect(20 * ind + (XBase + 100), ybase - 5, 18, 18, [fill |-> "lightgray", stroke |-> logEntryStroke(i,ind)]), 
                                   Text(20 * ind + (XBase + 105), ybase + 8, ToString(log[i][ind]), ("text-anchor" :>  "start" @@ "font-size" :> "12px"))>>, [h \in {} |-> {}])
logElem(i, ybase) == Group([ind \in DOMAIN log[i] |-> logEntry(i, ybase, ind)], [h \in {} |-> {}])
logElems ==  [i \in RMIdDomain |-> logElem(RMId[i], i * Spacing - 5)]


CrownIcon == "https://www.svgrepo.com/download/274106/crown.svg"

CrownElem(rmid, i) == Image(20, i * Spacing - 6, 15, 15, CrownIcon, IF state[rmid] # Primary THEN [hidden |-> "true"] ELSE <<>>)

cs == [i \in RMIdDomain |-> 
        LET rmid == ToString(RMId[i]) IN
        Group(<<
            Circle(XBase + 20, i * Spacing, 10, 
            [stroke |-> "black", fill |-> 
                IF state[rmid] = Primary 
                    THEN "gold" 
                ELSE IF state[rmid] = Secondary THEN "gray" 
                ELSE IF state[rmid] = Secondary THEN "red" ELSE "gray"]), 
            CrownElem(rmid,i)>>, [a \in {} |-> {}])]
labels == [i \in RMIdDomain |-> 
        LET rmid == RMId[i] IN 
            Text(XBase + 40, i * Spacing + 5, 
            ToString(rmid) \o ", t=" \o ToString(currentTerm[rmid]), \*\o ", " \o ToString(log[rmid]), 
            [fill |-> 
            IF state[rmid] = Primary 
                THEN "black" 
            ELSE IF state[RMId[i]] = Secondary THEN "black" 
            ELSE IF state[RMId[i]] = Secondary THEN "red" ELSE "gray"])]

\* 
\* The overall animation view as one big SVG element.
\* 
AnimView == Group(cs \o labels \o logElems, [transform |-> "translate(40, 40) scale(1.25)"])



=============================================================================

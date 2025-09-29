------------------------------- MODULE TwoPhase_anim ----------------------------- 
EXTENDS TLC, Naturals, Sequences, FiniteSets, TwoPhase

\* 
\* Animation definitions.
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

---------------------------------------------------------------------

CommitColor == "green"
AbortColor == "red"

\* Establish a fixed mapping to assign an ordering to elements in these sets.
\* ServerId == CHOOSE f \in [Server -> 1..Cardinality(Person)] : Injective(f)
RMId == CHOOSE f \in [1..Cardinality(RM) -> RM] : Injective(f)

\* Animation view definition.
c1 == Circle(10, 10, 3, [fill |-> "red"])
c2 == Circle(20, 10, 3, [fill |-> "red"])
\* ServerIdDomain == 1..Cardinality(Server)
RMIdDomain == 1..Cardinality(RM)

\* RM elements node circles with corresponding colors.
RMSpacing == 40
RMElems == [i \in RMIdDomain |-> Circle(RMSpacing * i, 45, 10, 
        [stroke |-> "black", fill |-> 
            IF rmState[RMId[i]] = "prepared" 
                THEN "steelblue" 
            ELSE IF rmState[RMId[i]] = "committed" THEN CommitColor 
            ELSE IF rmState[RMId[i]] = "aborted" THEN AbortColor ELSE "gray"])]

TMXpos == RMSpacing * (Cardinality(RM) + 1) \div 2
TMElem == Circle(TMXpos, 95, 10, [stroke |-> "black", fill |-> IF tmState = "committed" THEN CommitColor ELSE IF tmState = "init" THEN "gray" ELSE AbortColor])
RMTextElems == 
    [i \in RMIdDomain |->
        Text(40 * i, 30, RMId[i], ("fill" :> "black" @@ "text-anchor" :> "middle" @@ "font-size" :> "12"))
    ]
    \* <<Text(10, 10, "RM1", [fill |-> "black"]), Text(20, 10, "RM2", [fill |-> "black"]), Text(40, 50, "TM", [fill |-> "black"])>>
 
TMTextElems == <<
    Text(TMXpos, 80, "TM", ("fill" :> "black" @@ "text-anchor" :> "middle" @@ "font-size" :> "12")),
    Text(TMXpos, 120, ToString(tmPrepared), ("fill" :> "black" @@ "text-anchor" :> "middle" @@ "font-size" :> "10"))
>>
TextElems == RMTextElems \o TMTextElems


AnimView == Group(RMElems \o <<TMElem>> \o TextElems, [transform |-> "translate(40, 40) scale(1.25)"])

=============================================================================
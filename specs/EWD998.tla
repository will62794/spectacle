------------------------------- MODULE EWD998 -------------------------------
EXTENDS Integers, TLC, Sequences

CONSTANT N

Node == 0 .. N-1

Color == {"white", "black"}

VARIABLES 
    active,
    pending,
    color,
    counter,
    token

vars == <<active, pending, color, counter, token>>

TypeOK ==
    /\ active \in [Node -> BOOLEAN]
    /\ pending \in [Node -> Nat]
    /\ color \in [Node -> Color]
    /\ counter \in [Node -> Int]
    /\ token \in [ pos: Node, q: Int, color: Color ]

-----------------------------------------------------------------------------

Init ==
    /\ active \in [Node -> BOOLEAN]
    /\ pending = [i \in Node |-> 0]
    (* Rule 0 *)
    /\ color \in [Node -> Color]
    /\ counter = [i \in Node |-> 0]
    \* TODO: Address bug with repeated assignment here.
    \* /\ pending = [i \in Node |-> 0]
    /\ token = [pos |-> 0, q |-> 0, color |-> "black"]

-----------------------------------------------------------------------------

InitiateProbe ==
    (* Rules 1 + 5 + 6 *)
    /\ token.pos = 0
    /\ \* previous round inconclusive:
        \/ token.color = "black"
        \/ color[0] = "black"
        \/ counter[0] + token.q > 0
    /\ token' = [ pos |-> N-1, q |-> 0, color |-> "white"]
    /\ color' = [ color EXCEPT ![0] = "white" ]
    /\ UNCHANGED <<active, counter, pending>>                            

PassToken(i) ==
    (* Rules 2 + 4 + 7 *)
    /\ ~ active[i]
    /\ token.pos = i
    \* Rule 2 + 4
    /\ token' = [ pos |-> token["pos"] - 1, 
                    q |-> token["q"] + counter[i],
                color |-> IF color[i] = "black" THEN "black" ELSE token["color"] ]
    \* Rule 7
    /\ color' = [ color EXCEPT ![i] = "white" ]
    /\ UNCHANGED <<active, pending, counter>>

System ==
    \/ InitiateProbe
    \/ \E i \in Node \ {0}: PassToken(i)

-----------------------------------------------------------------------------

SendMsg(i, recv) ==
    /\ active[i]
    /\ counter' = [counter EXCEPT ![i] = @ + 1]
    /\ pending' = [pending EXCEPT ![recv] = @ + 1]
    /\ UNCHANGED <<active, color, token>>

\* Wakeup(i) in AsyncTerminationDetection.
RecvMsg(i) ==
    /\ pending[i] > 0
    /\ active' = [active EXCEPT ![i] = TRUE]
    /\ pending' = [pending EXCEPT ![i] = @ - 1]
    /\ counter' = [counter EXCEPT ![i] = @ - 1]
    /\ color' = [ color EXCEPT ![i] = "black" ]
    /\ UNCHANGED <<token>>

\* Terminate(i) in AsyncTerminationDetection.
Deactivate(i) ==
    /\ active[i]
    \* * ...in the next state (the prime operator ').
    \* * The previous expression didn't say anything about the other values of the
     \* * function, or even state that active' is a function (function update).
    /\ active' = [ active EXCEPT ![i] = FALSE ]
    \*/\ active' \in { f \in [ Node -> BOOLEAN] : \A n \in Node: ~active[n] => ~f[n] }
    \*//\ active' # active
    /\ UNCHANGED <<pending, color, counter, token>>

\* Environment == 
\*     \E n \in Node:
\*         \/ SendMsg(n)
\*         \/ RecvMsg(n)
\*         \/ Deactivate(n)

-----------------------------------------------------------------------------

\* Next ==
\*   \/ System 
\*   \/ Environment

Next ==
  \/ InitiateProbe
  \/ \E i \in Node \ {0} : PassToken(i)
  \/ \E n \in Node :  \E recv \in (Node \ {n}) : SendMsg(n, recv)
  \/ \E n \in Node : RecvMsg(n)
  \/ \E n \in Node : Deactivate(n)

Spec == Init /\ [][Next]_vars /\ WF_vars(System)

-----------------------------------------------------------------------------

terminated ==
    \A n \in Node : ~active[n] /\ pending[n] = 0

-----------------------------------------------------------------------------

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

Rect(x, y, w, h, attrs) == 
    LET svgAttrs == [x      |-> x, 
                     y      |-> y, 
                     width  |-> w, 
                     height |-> h] IN
    SVGElem("rect", Merge(svgAttrs, attrs), <<>>, "")

Line(x1, y1, x2, y2, attrs) == 
    LET svgAttrs == [x1 |-> x1, 
                     y1 |-> y1, 
                     x2 |-> x2,
                     y2 |-> y2] IN
    SVGElem("line", Merge(svgAttrs, attrs), <<>>, "")

\* Group element. 'children' is as a sequence of elements that will be contained in this group.
Group(children, attrs) == SVGElem("g", attrs, children, "")

-----------------------------------------------------------------------------

AnimNodes ==
    \* Domain 0..N-1 (Node) not supported by animation module.
    \* Offset by one to define a sequence instead.
    1..N

Coords ==
    LET area == 1000 
        base == 50
    IN [ n \in AnimNodes |-> IF n = 1 THEN [x|->0, y|->0]
                             ELSE IF n = 2 THEN [x|->base, y|->0]
                             ELSE [x|->base \div 2, y|-> (2 * area) \div base] ]

NodeCount == 
    [n \in AnimNodes |-> Text(Coords[n].x + 10, Coords[n].y + 15, ToString(counter[n-1]),
        ("fill" :> "black" @@ "text-anchor" :> "middle"))]

RingNetwork == 
    [n \in AnimNodes |-> Rect(Coords[n].x, Coords[n].y, 20, 20,
        [rx |-> IF ~active[n-1] THEN "0" ELSE "15",
         stroke |-> "black", opacity |-> "0.3",
         fill |-> color[n-1]])]

Token == 
    <<Circle(Coords[token.pos+1].x, Coords[token.pos+1].y, 5, 
        [stroke |-> "black", opacity |-> "0.3",
         fill |-> "black"])>>

MessageCount == 
    [n \in AnimNodes |-> Text(Coords[n].x, Coords[n].y, ToString(pending[n-1]),
        ("fill" :> "black" @@ "text-anchor" :> "middle" @@ "transform" :> "translate(22.5 18) scale(0.5 0.5)"))]

AnimView ==
    Group(NodeCount \o RingNetwork \o Token \o MessageCount, ("transform" :> "translate(40 40) scale(1.75 1.75)"))

=============================================================================

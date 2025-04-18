------------------------- MODULE CabbageGoatWolf -----------------------------
EXTENDS Naturals, FiniteSets, TLC, Sequences
\* Solving the https://en.wikipedia.org/wiki/Wolf,_goat_and_cabbage_problem
\* Modified from https://github.com/muratdem/PlusCal-examples/blob/master/Puzzles/CabbageGoatWolf_Pluscal.tla
    
Sides == {1,2}
C == "Cabbage"
G == "Goat"
W == "Wolf"
F == "Farmer"

Allowed(S) == 
    \/ F \in S 
    \/ (/\ ~ ( C \in S  /\  G \in S )
        /\ ~ ( G \in S  /\  W \in S ) )

VARIABLES banks, boat

(* define statement *)
SafeBoats(s) ==
    { B \in SUBSET banks[s]:
        /\ F \in B
        /\ Cardinality(B) <= 2
        /\ Allowed(banks[s] \ B) }

TypeOK ==
    /\ Cardinality(banks[1]) + Cardinality(banks[2]) + Cardinality(boat) = 4
    /\ Cardinality(boat) <=2
    /\ boat \in SUBSET {F,C,G,W}
    /\ banks[1] \in SUBSET {F,C,G,W}
    /\ banks[2] \in SUBSET {F,C,G,W}

NotSolved == Cardinality(banks[2]) < 4


vars == << banks, boat >>

ProcSet == (Sides)

Init == (* Global variables *)
        /\ banks = << {C,G,W,F}, {} >>
        /\ boat = {}

LoadBoat(self, P) == 
    /\ (banks[self]#{} /\  boat={})
    /\ boat' = P
    /\ banks' = [banks EXCEPT ![self] = banks[self] \ P]

EmptyBoat(self) == 
    /\ (boat#{})
    /\ banks' = [banks EXCEPT ![self] = banks[self] \union boat]
    /\ boat' = {}

Next == 
    \/ \E self \in Sides: EmptyBoat(self)
    \/ \E self \in Sides : \E P \in SafeBoats(self): LoadBoat(self, P)

Spec == Init /\ [][Next]_vars


------------------------------------------------------------
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

SetToSeq(S) == CHOOSE f \in [1..Cardinality(S) -> S] : Injective(f)

ActorIcon == (
    W :> "https://www.svgrepo.com/download/484119/wolf.svg" @@
    C :> "https://www.svgrepo.com/download/489683/cabbage.svg" @@
    G :> "https://www.svgrepo.com/download/401866/goat.svg" @@
    F :> "https://www.svgrepo.com/download/405360/farmer.svg"
)
BoatIcon == "https://www.svgrepo.com/download/487088/boat.svg"
RiverIcon == "https://www.svgrepo.com/download/493924/river.svg"
DangerIcon == "assets/danger-svgrepo-com.svg"
SuccessIcon == "https://www.svgrepo.com/download/404946/check-mark-button.svg"

Actors == {C,G,W,F}
ActorsOnSide(side) == {a \in Actors : a \in banks[side]}

\* ActorElem(actor, order) == Rect(10, order*20,10,10, <<>>)
actorWidth == 25
ActorElem(side, actor, order) == 
    IF side = "boat" 
    THEN Image(80, order*35,actorWidth,actorWidth, ActorIcon[actor], <<>>)
    ELSE Image((side-1)*140, order*35,actorWidth,actorWidth, ActorIcon[actor], <<>>)

\* Display danger icon if animals are left alone in unsafe configuration.
DangerElem(side) == Image((side-1)*140, 0, 30, 30, DangerIcon, [hidden |-> IF Allowed(banks[side]) THEN "hidden" ELSE "visible"])
SuccessElem(side) == Image((side-1)*145, 0, 13, 13, SuccessIcon, IF NotSolved THEN [hidden |-> "true"] ELSE <<>>)

SideElem(side) == 
    Group(SetToSeq({ 
        LET order == CHOOSE f \in [ActorsOnSide(side) -> 1..Cardinality(ActorsOnSide(side))] : Injective(f) IN 
            ActorElem(side, a, order[a]) : a \in ActorsOnSide(side)
        }) \o <<DangerElem(side)>>, [i \in {} |-> {}])

BoatActorElems == 
    Group(SetToSeq({
        LET order == CHOOSE f \in [boat -> 1..Cardinality(boat)] : Injective(f) IN  
        ActorElem("boat", a, order[a]) : a \in boat
        }), [i \in {} |-> {}])
    
BoatElem == 
    Group(<<
        \* Image(50, 5, 80, 180, BoatIcon, <<>>), 
        BoatActorElems>>, [i \in {} |-> {}])
RiverElem == Image(55, 5, 80, 80, RiverIcon, [style |-> "opacity:0.3;transform:scale(1,1.75); /* W3C */"])

AnimView == Group(<<SideElem(1), SideElem(2), SuccessElem(2), RiverElem, BoatElem>>, [i \in {} |-> {}])



============================================================

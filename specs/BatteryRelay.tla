
## Battery Relay: Can You Help The Valets?

Four vehicles are stranded in a parking garage with dead batteries, and all of the charging
stations are currently occupied. It's nearly 4:45 PM, and their owners are eager to head home
at 5pm.

Thankfully, the valets have a spare battery—just enough to jump-start one vehicle and drive it
to another garage, where a fleet charger can instantly recharge all four vehicles at once.
The catch? It's all or nothing: the charger only works if all four vehicles arrive together.

There's not enough time to shuttle each vehicle one by one. However, the valets can tow a
second vehicle behind a running one—but only if the towing vehicle is large enough. A smaller
vehicle can't tow a larger one.

Can you figure out the best way for the valets to move all four vehicles to the other garage
in a single trip?

-------------------------------- MODULE BatteryRelay --------------------------------
EXTENDS Naturals, FiniteSets, FiniteSetsExt, TLC

MaxLevel == 17

Cost == [
    Truck |-> 10,
    Car   |-> 5,
    Bike  |-> 2,
    Scooter |-> 1
]

VARIABLES left, right, batteryLeft, batteryLevel
vars == <<left, right, batteryLeft, batteryLevel>>

Vehicles == DOMAIN Cost

TypeOK ==
    /\ left \subseteq Vehicles
    /\ right \subseteq Vehicles
    /\ batteryLeft \in BOOLEAN 
    /\ batteryLevel \in Nat

(* Initial state: all Vehicles and the battery are on the left side.
   The spare battery is fully charged.   *)
Init ==
    /\ left = Vehicles
    /\ right = {}
    /\ batteryLeft = TRUE
    /\ batteryLevel = MaxLevel

(* Action: from one or two vehicles left to right *)
LeftToRight(group, cost) ==
    (* Before the move: *)
    (* The group must be non-empty and contain at most two vehicles *)
    /\ Cardinality(group) \in 1..2
    (* Can only move vehicles to the right that are on the left side *)
    /\ group \in SUBSET left
    (* The battery has to be left *)
    /\ batteryLeft = TRUE
    (* After the move: *)
    (* The battery will be on the right side *)
    /\ batteryLeft' = ~batteryLeft
    (* The group of vehicles will be removed from the left side *)
    /\ left' = left \ group
    (* The group of vehicles will be added to the right side *)
    /\ right' = right \union group
    (* The battery will be decreased by the cost of moving the 
       biggest vehicle of the group *)
    /\ batteryLevel' = batteryLevel - cost

(* Action: from right to left *)
RightToLeft(group, cost) ==
    /\ Cardinality(group) \in 1..2
    /\ group \in SUBSET right
    /\ batteryLeft = FALSE
    /\ batteryLeft' = ~batteryLeft
    /\ right' = right \ group
    /\ left' = left \union group
    /\ batteryLevel' = batteryLevel - cost

(* Next-state relation *)
Next ==
    \/ \E group \in (SUBSET Vehicles) \ {{}} :
        \E c \in {Max({ Cost[g] : g \in group })} :
            LeftToRight(group, c)
    \/ \E group \in (SUBSET Vehicles) \ {{}} :
        \E c \in {Max({ Cost[g] : g \in group })} :
            RightToLeft(group, c)

(* Safety: Vehicles cannot be on both sides and don't disappear or duplicate *)
Safety ==
    /\ left \intersect right = {}
    /\ left \union right = Vehicles

(* All Vehicles are on the right side and the battery is not depleted *)
Solution ==
    /\ right = Vehicles
    /\ batteryLevel >= 0

(* This invariant will be violated when we find a solution *)
NoSolution ==
    ~Solution

(* Specification *)
Spec == 
    Init /\ [][Next]_vars







------------------------------------------------------------
\* The following definitions are used to generate the SVG.
\* Feel free to ignore.
\* 


\* Merge two records
Merge(r1, r2) == 
    LET D1 == DOMAIN r1 D2 == DOMAIN r2 IN
    [k \in (D1 \cup D2) |-> IF k \in D1 THEN r1[k] ELSE r2[k]]

SVGElem(_name, _attrs, _children, _innerText) == 
    [name |-> _name, attrs |-> _attrs, children |-> _children, innerText |-> _innerText ]

Text(x, y, text, attrs) == 
    (**************************************************************************)
    (* Text element.'x' and 'y' should be given as integers, and 'text' given *)
    (* as a string.                                                           *)
    (**************************************************************************)
    LET svgAttrs == [x |-> x, 
                     y |-> y] IN
    SVGElem("text", Merge(svgAttrs, attrs), <<>>, text) 

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

-------

iconSize == 25

VehicleIcon(v) == 
    IF v = "Truck" THEN "https://www.svgrepo.com/download/59774/loaded-truck.svg"
    ELSE IF v = "Car" THEN "https://www.svgrepo.com/download/455224/fast-car.svg"
    ELSE IF v = "Bike" THEN "https://www.svgrepo.com/download/11226/motorbike.svg"
    ELSE IF v = "Scooter" THEN "https://www.svgrepo.com/download/62546/scooter.svg"
    ELSE "https://www.svgrepo.com/download/438355/car.svg"

Left ==
    LET order == CHOOSE f \in [left -> 1..Cardinality(left)] : Injective(f)
        image(actor, o) == Image(10, o*35,iconSize,iconSize, VehicleIcon(actor), <<>>) IN
    Group(SetToSeq({image(p, order[p]) : p \in left}), [i \in {} |-> {}])

Right ==
    LET order == CHOOSE f \in [right -> 1..Cardinality(right)] : Injective(f)
        image(actor, o) == Image(130, o*35,iconSize,iconSize, VehicleIcon(actor), <<>>) IN
    Group(SetToSeq({image(p, order[p]) : p \in right}), [i \in {} |-> {}])

BatteryIcon ==
    IF batteryLevel > 12 THEN "https://www.svgrepo.com/download/532833/battery-full.svg"
    ELSE IF batteryLevel > 7 THEN "https://www.svgrepo.com/download/532837/battery-mid.svg"
    ELSE IF batteryLevel > 0 THEN "https://www.svgrepo.com/download/532836/battery-low.svg"
    ELSE "https://www.svgrepo.com/download/532834/battery-empty.svg"

Battery ==
   IF batteryLeft
   THEN Group(<<Image(10,  5, iconSize, iconSize, BatteryIcon, <<>>), 
                Text( 35, 23, ToString(batteryLevel), <<>>)>>, [i \in {} |-> {}])
   ELSE Group(<<Image(130, 5, iconSize, iconSize, BatteryIcon, <<>>), 
                Text(155, 23, ToString(batteryLevel), <<>>)>>, [i \in {} |-> {}])

Chargers ==
   Group(SetToSeq({
   	Image(160, i, 30, 30, IF right = Vehicles 
                          THEN "https://www.svgrepo.com/download/325164/ev-plug-charging.svg"
                          ELSE "https://www.svgrepo.com/download/325166/ev-plug-error.svg", <<>>)
                            : i \in {40 + (i*35) : i \in 0..Cardinality(Vehicles)-1}
   }), [i \in {} |-> {}])

Empty ==
   Image(13, 20, 140, 140, "https://www.svgrepo.com/download/442077/battery-empty-symbolic.svg",
                            IF batteryLevel < 0 THEN <<>> ELSE [hidden |-> "true"] )

AnimView == Group(<<Left, Right, Battery, Chargers, Empty>>, [i \in {} |-> {}])

====

---- MODULE BatteryRelay_anim ----
EXTENDS TLC, BatteryRelay


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

-------

iconSize == 25

VehicleIcon(v) == 
    IF v = "Truck" THEN "https://www.svgrepo.com/download/59774/loaded-truck.svg"
    ELSE IF v = "Car" THEN "https://www.svgrepo.com/download/455224/fast-car.svg"
    ELSE IF v = "Bike" THEN "https://www.svgrepo.com/download/11226/motorbike.svg"
    ELSE IF v = "Scooter" THEN "https://www.svgrepo.com/download/62546/scooter.svg"
    ELSE "https://www.svgrepo.com/download/438355/car.svg"

Left ==
    LET order == SetToSeq(left)
        image(actor, o) == Image(10, o*35,iconSize,iconSize, VehicleIcon(actor), <<>>) IN
    Group(SetToSeq({image(p, (CHOOSE i \in DOMAIN order : order[i] = p)) : p \in left}), [i \in {} |-> {}])

Right ==
    LET order == SetToSeq(right)
        image(actor, o) == Image(130, o*35,iconSize,iconSize, VehicleIcon(actor), <<>>) IN
    Group(SetToSeq({image(p, (CHOOSE i \in DOMAIN order : order[i] = p)) : p \in right}), [i \in {} |-> {}])

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
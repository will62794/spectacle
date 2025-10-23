---- MODULE BatteryRelay_anim ----
EXTENDS TLC, SVG, SequencesExt, BatteryRelay

iconSize == 25

VehicleIcon(v) == 
    IF v = "Truck" THEN "https://www.svgrepo.com/show/59774/loaded-truck.svg"
    ELSE IF v = "Car" THEN "https://www.svgrepo.com/show/455224/fast-car.svg"
    ELSE IF v = "Bike" THEN "https://www.svgrepo.com/show/11226/motorbike.svg"
    ELSE IF v = "Scooter" THEN "https://www.svgrepo.com/show/62546/scooter.svg"
    ELSE "https://www.svgrepo.com/show/438355/car.svg"

Left ==
    LET order == SetToSeq(left)
        image(actor, o) == Image(10, o*35,iconSize,iconSize, VehicleIcon(actor), <<>>) IN
    Group(SetToSeq({image(p, (CHOOSE i \in DOMAIN order : order[i] = p)) : p \in left}), [i \in {} |-> {}])

Right ==
    LET order == SetToSeq(right)
        image(actor, o) == Image(130, o*35,iconSize,iconSize, VehicleIcon(actor), <<>>) IN
    Group(SetToSeq({image(p, (CHOOSE i \in DOMAIN order : order[i] = p)) : p \in right}), [i \in {} |-> {}])

BatteryIcon ==
    IF batteryLevel > 12 THEN "https://www.svgrepo.com/show/532833/battery-full.svg"
    ELSE IF batteryLevel > 7 THEN "https://www.svgrepo.com/show/532837/battery-mid.svg"
    ELSE IF batteryLevel > 0 THEN "https://www.svgrepo.com/show/532836/battery-low.svg"
    ELSE "https://www.svgrepo.com/show/532834/battery-empty.svg"

Battery ==
   IF batteryLeft
   THEN Group(<<Image(10,  5, iconSize, iconSize, BatteryIcon, <<>>), 
                Text( 35, 23, ToString(batteryLevel), <<>>)>>, [i \in {} |-> {}])
   ELSE Group(<<Image(130, 5, iconSize, iconSize, BatteryIcon, <<>>), 
                Text(155, 23, ToString(batteryLevel), <<>>)>>, [i \in {} |-> {}])

Chargers ==
   Group(SetToSeq({
   	Image(160, i, 30, 30, IF right = Vehicles 
                          THEN "https://www.svgrepo.com/show/325164/ev-plug-charging.svg"
                          ELSE "https://www.svgrepo.com/show/325166/ev-plug-error.svg", <<>>)
                            : i \in {40 + (i*35) : i \in 0..Cardinality(Vehicles)-1}
   }), [i \in {} |-> {}])

Empty ==
   Image(13, 20, 140, 140, "https://www.svgrepo.com/show/442077/battery-empty-symbolic.svg",
                            IF batteryLevel < 0 THEN <<>> ELSE [hidden |-> "true"] )

AnimView == Group(<<Left, Right, Battery, Chargers, Empty>>, [i \in {} |-> {}])

\* Animation alias for generating SVG files with TLC
AnimAlias ==
    [
        left |-> left,
        right |-> right,
        batteryLeft |-> batteryLeft,
        batteryLevel |-> batteryLevel        
    ] @@ 
    LET IO == INSTANCE IOUtils IN
    [ _anim |-> IO!Serialize("<svg viewBox='0 0 230 200' xmlns='http://www.w3.org/2000/svg' xmlns:xlink='http://www.w3.org/1999/xlink'>" \o 
                         SVGElemToString(AnimView) \o 
                         "</svg>", 
                         "BatteryRelay_anim_" \o ToString(TLCGet("level")) \o ".svg",
                         [format |-> "TXT", charset |-> "UTF-8", openOptions |-> <<"WRITE", "CREATE", "TRUNCATE_EXISTING">>]) ]

====
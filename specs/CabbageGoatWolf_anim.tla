---- MODULE CabbageGoatWolf_anim ----
EXTENDS TLC, SVG, SequencesExt, Functions, CabbageGoatWolf

ActorIcon == (
    W :> "https://www.svgrepo.com/show/484119/wolf.svg" @@
    C :> "https://www.svgrepo.com/show/489683/cabbage.svg" @@
    G :> "https://www.svgrepo.com/show/401866/goat.svg" @@
    F :> "https://www.svgrepo.com/show/405360/farmer.svg"
)
BoatIcon == "https://www.svgrepo.com/show/487088/boat.svg"
RiverIcon == "https://www.svgrepo.com/show/493924/river.svg"
DangerIcon == "https://www.svgrepo.com/show/474712/warning.svg"
SuccessIcon == "https://www.svgrepo.com/show/404946/check-mark-button.svg"

Actors == {C,G,W,F}
ActorsOnSide(side) == {a \in Actors : a \in banks[side]}

\* ActorElem(actor, order) == Rect(10, order*20,10,10, <<>>)
actorWidth == 25
ActorElem(side, actor, order) == 
    IF side = 3
    THEN Image(80, order*35,actorWidth,actorWidth, ActorIcon[actor], <<>>)
    ELSE Image((side-1)*140, order*35,actorWidth,actorWidth, ActorIcon[actor], <<>>)

\* Display danger icon if animals are left alone in unsafe configuration.
DangerElem(side) == Image((side-1)*140, 0, 30, 30, DangerIcon, [hidden |-> IF Allowed(banks[side]) THEN "hidden" ELSE "visible"])
SuccessElem(side) == Image((side-1)*145, 0, 13, 13, SuccessIcon, IF NotSolved THEN [hidden |-> "true"] ELSE <<>>)

SideElem(side) == 
    Group(SetToSeq({ 
        LET order == CHOOSE f \in [ActorsOnSide(side) -> 1..Cardinality(ActorsOnSide(side))] : IsInjective(f) IN 
            ActorElem(side, a, order[a]) : a \in ActorsOnSide(side)
        }) \o <<DangerElem(side)>>, [i \in {} |-> {}])

BoatActorElems == 
    Group(SetToSeq({
        LET order == CHOOSE f \in [boat -> 1..Cardinality(boat)] : IsInjective(f) IN  
        ActorElem(3, a, order[a]) : a \in boat
        }), [i \in {} |-> {}])
    
BoatElem == 
    Group(<<
        \* Image(50, 5, 80, 180, BoatIcon, <<>>), 
        BoatActorElems>>, [i \in {} |-> {}])
RiverElem == Image(55, 5, 80, 80, RiverIcon, [style |-> "opacity:0.3;transform:scale(1,1.75); /* W3C */"])

AnimView == Group(<<SideElem(1), SideElem(2), SuccessElem(2), RiverElem, BoatElem>>, [transform |-> "translate(60, 40) scale(1.75)"])

\* Animation alias for generating SVG files with TLC.
AnimAlias ==
    [
        banks |-> banks, boat |-> boat
    ] @@
    LET IO == INSTANCE IOUtils IN
    [ _anim |-> IO!Serialize("<svg viewBox='0 0 530 420' xmlns='http://www.w3.org/2000/svg' xmlns:xlink='http://www.w3.org/1999/xlink'>" \o 
                         SVGElemToString(AnimView) \o 
                         "</svg>", 
                         "CabbageGoatWolf_anim_" \o ToString(TLCGet("level")) \o ".svg",
                         [format |-> "TXT", charset |-> "UTF-8", openOptions |-> <<"WRITE", "CREATE", "TRUNCATE_EXISTING">>]) ]

====

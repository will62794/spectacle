------------------------------- MODULE TwoPhase_anim ----------------------------- 
EXTENDS TLC, Naturals, Sequences, Functions, FiniteSets, SVG, TwoPhase

PrepareColor == "steelblue"
CommitColor == "green"
AbortColor == "red"

\* Establish a fixed mapping to assign an ordering to elements in these sets.
\* ServerId == CHOOSE f \in [Server -> 1..Cardinality(Person)] : Injective(f)
RMId == CHOOSE f \in [1..Cardinality(RM) -> RM] : IsInjective(f)

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
                THEN PrepareColor 
            ELSE IF rmState[RMId[i]] = "committed" THEN CommitColor 
            ELSE IF rmState[RMId[i]] = "aborted" THEN AbortColor ELSE "gray"])]

TMXpos == RMSpacing * ((Cardinality(RM) + 1) \div 2)
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

\* Animation alias for generating SVG files with TLC.
AnimAlias ==
    [
        rmState |-> rmState, tmState |-> tmState, tmPrepared |-> tmPrepared, msgs |-> msgs
    ] @@
    [ _anim |-> SVGSerialize(SVGDoc(AnimView, 0, 0, 180, 200, <<>>), "TwoPhase_anim_", TLCGet("level"))]

=============================================================================

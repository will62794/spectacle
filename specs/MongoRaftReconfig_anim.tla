---- MODULE MongoRaftReconfig_anim ----
\*
\* High level specification of Raft protocol with dynamic reconfiguration.
\*

EXTENDS SVG, SequencesExt, MongoRaftReconfig

Spacing == 40

CrownIcon == "https://www.svgrepo.com/show/274106/crown.svg"
BugIcon == "https://www.svgrepo.com/show/525701/bug-minimalistic.svg"

CrownElem(xbase, rmid, i) == Image(xbase, i * Spacing - 6, 13, 13, CrownIcon, IF state[rmid] # Primary THEN [hidden |-> "true"] ELSE <<>>)

\* Establish a fixed mapping to assign an ordering to elements in these sets.
\* ServerId == CHOOSE f \in [Server -> 1..Cardinality(Person)] : Injective(f)
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

\* Animation alias for generating SVG files with TLC.
AnimAlias ==
    [
        currentTerm |-> currentTerm, state |-> state, log |-> log, immediatelyCommitted |-> immediatelyCommitted, config |-> config, configVersion |-> configVersion, configTerm |-> configTerm
    ] @@
    LET IO == INSTANCE IOUtils IN
    [ _anim |-> IO!Serialize("<svg viewBox='0 0 720 350' xmlns='http://www.w3.org/2000/svg' xmlns:xlink='http://www.w3.org/1999/xlink'>" \o 
                         SVGElemToString(AnimView) \o 
                         "</svg>", 
                         "MongoRaftReconfig_anim_" \o ToString(TLCGet("level")) \o ".svg",
                         [format |-> "TXT", charset |-> "UTF-8", openOptions |-> <<"WRITE", "CREATE", "TRUNCATE_EXISTING">>]) ]

=============================================================================

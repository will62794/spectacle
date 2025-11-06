Claude-4.1-opus:

### Prompt 1:

```
Propose a layout for a TLA+ animation that illustrates the AWS outage scenario described in @AwsDNSRace.md, based on the TLA+ specification @AwsDNSRace.tla.

Refer to the TLA+ MCP resources and their manual on creating animations to guide your proposal.
```

### Prompt 2: 

```
Generate the animation for the counterexample to NeverDeleteActive.
```

------------------------------ MODULE AwsDNSRace_anim ------------------------------
EXTENDS Naturals, Sequences, TLC, SVG, IOUtils, FiniteSets, AwsDNSRace

(***************************************************************************)
(* Animation layout for AWS DNS Race Condition                             *)
(* This animation visualizes:                                              *)
(*   1. DNS Planner generating plans                                       *)
(*   2. Multiple DNS Enactors processing plans                            *)
(*   3. Plan queue showing pending plans                                   *)
(*   4. Current active plan in Route53                                     *)
(*   5. Plan timeline showing versions and deletion status                 *)
(*   6. Race condition indicators                                          *)
(***************************************************************************)

\* ============================================================================
\* Layout Constants
\* ============================================================================

\* Canvas dimensions
CanvasWidth == 1200
CanvasHeight == 800

\* Component positioning
PlannerX == 100
PlannerY == 100

QueueX == 300
QueueY == 80
QueueSpacing == 40

EnactorBaseX == 550
EnactorY == 100
EnactorSpacing == 150

Route53X == 900
Route53Y == 100

TimelineX == 100
TimelineY == 400
TimelineSpacing == 60

\* Visual constants
NodeRadius == 30
SmallRadius == 20
PlanBoxWidth == 50
PlanBoxHeight == 30

\* ============================================================================
\* Helper Functions
\* ============================================================================

\* Convert sets to sequences for deterministic rendering
EnactorSeq == CHOOSE seq \in [1..Cardinality(ENACTORS) -> ENACTORS] : 
    \A i, j \in 1..Cardinality(ENACTORS) : i # j => seq[i] # seq[j]
EnactorToIndex(e) == CHOOSE i \in 1..Len(EnactorSeq) : EnactorSeq[i] = e

\* Color schemes for different states
PlannerColor == "steelblue"
EnactorColor(e) == 
    CASE enactor_pc[e] = 0 -> "#90EE90"  \* Light green - idle
      [] enactor_pc[e] = 1 -> "#FFD700"  \* Gold - applying
      [] enactor_pc[e] = 2 -> "#FF6347"  \* Tomato - cleanup
      [] OTHER -> "gray"

PlanColor(plan) == 
    IF plan = current_plan THEN "#32CD32"  \* Lime green - active
    ELSE IF plan_deleted[plan] THEN "#DC143C"  \* Crimson - deleted
    ELSE "#87CEEB"  \* Sky blue - available

QueuePlanColor(plan) == "#B0C4DE"  \* Light steel blue

\* State labels for enactors
EnactorStateLabel(e) ==
    CASE enactor_pc[e] = 0 -> "Idle"
      [] enactor_pc[e] = 1 -> "Applying"
      [] enactor_pc[e] = 2 -> "Cleanup"
      [] OTHER -> "Unknown"

\* ============================================================================
\* Visual Components
\* ============================================================================

\* DNS Planner visualization
PlannerComponent == Group(<<
    \* Planner node
    Circle(PlannerX, PlannerY, NodeRadius, 
        ("fill" :> PlannerColor @@ "stroke" :> "black" @@ "stroke-width" :> "2")),
    Text(PlannerX, PlannerY + 5, "DNS Planner", 
        ("text-anchor" :> "middle" @@ "font-size" :> "14px" @@ "font-weight" :> "bold")),
    \* Latest plan indicator
    Text(PlannerX, PlannerY + 60, "Latest: " \o ToString(latest_plan), 
        ("text-anchor" :> "middle" @@ "font-size" :> "12px"))
>>, <<>>)

\* Plan Queue visualization
QueueComponent == 
    LET queueElems == [i \in 1..Len(plan_channel) |->
        Group(<<
            Rect(QueueX, QueueY + (i-1) * QueueSpacing, PlanBoxWidth, PlanBoxHeight,
                ("fill" :> QueuePlanColor(plan_channel[i]) @@ 
                 "stroke" :> "black" @@ "stroke-width" :> "1")),
            Text(QueueX + PlanBoxWidth \div 2, QueueY + (i-1) * QueueSpacing + 20, 
                ToString(plan_channel[i]),
                ("text-anchor" :> "middle" @@ "font-size" :> "12px"))
        >>, <<>>)
    ] IN
    Group(<<
        Text(QueueX + PlanBoxWidth \div 2, QueueY - 20, "Plan Queue", 
            ("text-anchor" :> "middle" @@ "font-size" :> "14px" @@ "font-weight" :> "bold")),
        Group(queueElems, <<>>)
    >>, <<>>)

\* DNS Enactors visualization
EnactorComponents == 
    LET enactorElems == [i \in 1..Len(EnactorSeq) |->
        LET e == EnactorSeq[i]
            xPos == EnactorBaseX + (i-1) * EnactorSpacing
        IN Group(<<
            \* Enactor node
            Circle(xPos, EnactorY, NodeRadius, 
                ("fill" :> EnactorColor(e) @@ "stroke" :> "black" @@ "stroke-width" :> "2")),
            Text(xPos, EnactorY, ToString(e), 
                ("text-anchor" :> "middle" @@ "font-size" :> "14px" @@ "font-weight" :> "bold")),
            \* State label
            Text(xPos, EnactorY + 45, EnactorStateLabel(e), 
                ("text-anchor" :> "middle" @@ "font-size" :> "12px")),
            \* Processing plan indicator
            IF enactor_processing[e] > 0 THEN
                Text(xPos, EnactorY + 60, "Plan: " \o ToString(enactor_processing[e]), 
                    ("text-anchor" :> "middle" @@ "font-size" :> "11px" @@ 
                     "font-weight" :> "bold" @@ "fill" :> "darkblue"))
            ELSE
                Text(xPos, EnactorY + 60, "No plan", 
                    ("text-anchor" :> "middle" @@ "font-size" :> "11px" @@ "fill" :> "gray"))
        >>, <<>>)
    ] IN
    Group(enactorElems, <<>>)

\* Route53 DNS State visualization
Route53Component == Group(<<
    \* Route53 node
    Rect(Route53X - 40, Route53Y - 40, 80, 80,
        ("fill" :> "#FF9500" @@ "stroke" :> "black" @@ 
         "stroke-width" :> "2" @@ "rx" :> "10")),
    Text(Route53X, Route53Y - 10, "Route53", 
        ("text-anchor" :> "middle" @@ "font-size" :> "14px" @@ "font-weight" :> "bold")),
    \* Current plan display
    IF current_plan > 0 THEN
        Group(<<
            Text(Route53X, Route53Y + 10, "Active Plan", 
                ("text-anchor" :> "middle" @@ "font-size" :> "12px")),
            Circle(Route53X, Route53Y + 30, SmallRadius \div 2, 
                ("fill" :> PlanColor(current_plan) @@ "stroke" :> "black")),
            Text(Route53X, Route53Y + 35, ToString(current_plan), 
                ("text-anchor" :> "middle" @@ "font-size" :> "14px" @@ 
                 "font-weight" :> "bold" @@ "fill" :> "white"))
        >>, <<>>)
    ELSE
        Text(Route53X, Route53Y + 20, "No active plan", 
            ("text-anchor" :> "middle" @@ "font-size" :> "12px" @@ "fill" :> "red"))
>>, <<>>)

\* Plan Timeline visualization
TimelineComponent ==
    LET planElems == [p \in 1..MAX_PLAN |->
        IF p <= latest_plan THEN
            LET xPos == TimelineX + (p-1) * TimelineSpacing IN
            Group(<<
                \* Plan box
                Rect(xPos, TimelineY, PlanBoxWidth, PlanBoxHeight,
                    ("fill" :> PlanColor(p) @@ "stroke" :> "black" @@ 
                     "stroke-width" :> IF p = current_plan THEN "3" ELSE "1")),
                \* Plan number
                Text(xPos + PlanBoxWidth \div 2, TimelineY + 20, ToString(p),
                    ("text-anchor" :> "middle" @@ "font-size" :> "12px" @@ 
                     "font-weight" :> "bold")),
                \* Status indicator
                IF plan_deleted[p] THEN
                    Text(xPos + PlanBoxWidth \div 2, TimelineY + 45, "DELETED",
                        ("text-anchor" :> "middle" @@ "font-size" :> "10px" @@ 
                         "fill" :> "red" @@ "font-weight" :> "bold"))
                ELSE IF p = current_plan THEN
                    Text(xPos + PlanBoxWidth \div 2, TimelineY + 45, "ACTIVE",
                        ("text-anchor" :> "middle" @@ "font-size" :> "10px" @@ 
                         "fill" :> "green" @@ "font-weight" :> "bold"))
                ELSE
                    Text(xPos + PlanBoxWidth \div 2, TimelineY + 45, "available",
                        ("text-anchor" :> "middle" @@ "font-size" :> "10px" @@ 
                         "fill" :> "gray"))
            >>, <<>>)
        ELSE
            Group(<<>>, <<>>)
    ] IN
    Group(<<
        Text(TimelineX, TimelineY - 20, "Plan Timeline", 
            ("text-anchor" :> "start" @@ "font-size" :> "16px" @@ "font-weight" :> "bold")),
        Group(planElems, <<>>),
        \* Highest applied indicator
        Text(TimelineX, TimelineY + 80, 
            "Highest Applied: " \o ToString(highest_plan_applied),
            ("text-anchor" :> "start" @@ "font-size" :> "12px"))
    >>, <<>>)

\* Connection arrows
ConnectionArrows == Group(<<
    \* Planner to Queue
    SVGElem("line", 
        ("x1" :> ToString(PlannerX + NodeRadius) @@ 
         "y1" :> ToString(PlannerY) @@
         "x2" :> ToString(QueueX - 10) @@ 
         "y2" :> ToString(QueueY + 15) @@
         "stroke" :> "black" @@ 
         "stroke-width" :> "2" @@
         "marker-end" :> "url(#arrowhead)"),
        <<>>, ""),
    \* Queue to Enactors
    SVGElem("line", 
        ("x1" :> ToString(QueueX + PlanBoxWidth + 10) @@ 
         "y1" :> ToString(QueueY + 15) @@
         "x2" :> ToString(EnactorBaseX - NodeRadius - 10) @@ 
         "y2" :> ToString(EnactorY) @@
         "stroke" :> "black" @@ 
         "stroke-width" :> "2" @@
         "marker-end" :> "url(#arrowhead)"),
        <<>>, ""),
    \* Enactors to Route53
    SVGElem("line", 
        ("x1" :> ToString(EnactorBaseX + EnactorSpacing + NodeRadius) @@ 
         "y1" :> ToString(EnactorY) @@
         "x2" :> ToString(Route53X - 50) @@ 
         "y2" :> ToString(Route53Y) @@
         "stroke" :> "black" @@ 
         "stroke-width" :> "2" @@
         "marker-end" :> "url(#arrowhead)"),
        <<>>, "")
>>, <<>>)

\* Warning indicator for race condition
RaceConditionWarning ==
    IF /\ current_plan > 0 
       /\ plan_deleted[current_plan] THEN
        Group(<<
            Rect(400, 250, 400, 80,
                ("fill" :> "#FFE4B5" @@ "stroke" :> "red" @@ 
                 "stroke-width" :> "3" @@ "rx" :> "10")),
            Text(600, 280, "⚠️ RACE CONDITION DETECTED! ⚠️",
                ("text-anchor" :> "middle" @@ "font-size" :> "18px" @@ 
                 "font-weight" :> "bold" @@ "fill" :> "red")),
            Text(600, 305, "Active plan " \o ToString(current_plan) \o " has been deleted!",
                ("text-anchor" :> "middle" @@ "font-size" :> "14px" @@ "fill" :> "darkred"))
        >>, <<>>)
    ELSE
        Group(<<>>, <<>>)

\* Legend
Legend == Group(<<
    Text(50, 600, "Legend:", 
        ("font-size" :> "14px" @@ "font-weight" :> "bold")),
    \* Enactor states
    Circle(50, 630, 10, ("fill" :> "#90EE90" @@ "stroke" :> "black")),
    Text(70, 635, "Enactor: Idle", ("font-size" :> "12px")),
    Circle(50, 655, 10, ("fill" :> "#FFD700" @@ "stroke" :> "black")),
    Text(70, 660, "Enactor: Applying", ("font-size" :> "12px")),
    Circle(50, 680, 10, ("fill" :> "#FF6347" @@ "stroke" :> "black")),
    Text(70, 685, "Enactor: Cleanup", ("font-size" :> "12px")),
    \* Plan states
    Rect(200, 620, 30, 20, ("fill" :> "#32CD32" @@ "stroke" :> "black")),
    Text(240, 635, "Active Plan", ("font-size" :> "12px")),
    Rect(200, 645, 30, 20, ("fill" :> "#DC143C" @@ "stroke" :> "black")),
    Text(240, 660, "Deleted Plan", ("font-size" :> "12px")),
    Rect(200, 670, 30, 20, ("fill" :> "#87CEEB" @@ "stroke" :> "black")),
    Text(240, 685, "Available Plan", ("font-size" :> "12px"))
>>, <<>>)

\* ============================================================================
\* Main Animation View
\* ============================================================================

AnimView == 
    Group(<<
        \* Arrow marker definition
        SVGElem("defs", <<>>, <<
            SVGElem("marker", 
                ("id" :> "arrowhead" @@ 
                 "markerWidth" :> "10" @@ 
                 "markerHeight" :> "7" @@
                 "refX" :> "9" @@ 
                 "refY" :> "3.5" @@
                 "orient" :> "auto"),
                <<SVGElem("polygon", 
                    ("points" :> "0 0, 10 3.5, 0 7" @@ 
                     "fill" :> "black"), 
                    <<>>, "")>>, 
                "")
        >>, ""),
        \* Title
        Text(CanvasWidth \div 2, 30, "AWS DNS Race Condition Visualization",
            ("text-anchor" :> "middle" @@ "font-size" :> "24px" @@ 
             "font-weight" :> "bold")),
        \* Components
        PlannerComponent,
        QueueComponent,
        EnactorComponents,
        Route53Component,
        TimelineComponent,
        ConnectionArrows,
        RaceConditionWarning,
        Legend
    >>, <<>>)

\* ============================================================================
\* Animation Alias for TLC
\* ============================================================================

AnimAlias ==
    [state |-> 
        [current_plan |-> current_plan,
         latest_plan |-> latest_plan,
         highest_plan_applied |-> highest_plan_applied,
         plan_deleted |-> plan_deleted,
         plan_channel |-> plan_channel,
         enactor_processing |-> enactor_processing,
         enactor_pc |-> enactor_pc]] @@
    [_anim |-> Serialize(
        "<svg viewBox='0 0 " \o ToString(CanvasWidth) \o " " \o 
        ToString(CanvasHeight) \o "' xmlns='http://www.w3.org/2000/svg'>" \o 
        SVGElemToString(AnimView) \o "</svg>", 
        "AwsDNSRace_anim_" \o ToString(TLCGet("level")) \o ".svg",
        [format |-> "TXT", charset |-> "UTF-8", 
         openOptions |-> <<"WRITE", "CREATE", "TRUNCATE_EXISTING">>])]

============================== MODULE AwsDNSRace_anim ==============================

------------------------------- MODULE EWD998 -------------------------------
EXTENDS Integers, TLC, Sequences, SVG, IOUtils

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

\* SVG functions are provided by the SVG module - no need to redefine them

\* Empty element sequence for cleaner code
Empty == <<>>

-----------------------------------------------------------------------------

AnimNodes ==
    \* Domain 0..N-1 (Node) not supported by animation module.
    \* Offset by one to define a sequence instead.
    1..N

\* Calculate positioning for nodes in a ring layout
\* Using predefined positions for common node counts, with fallback for larger rings
Coords ==
    LET centerX == 200
        centerY == 300
        radius == 120
    IN [n \in AnimNodes |-> 
        IF N = 1 THEN [x |-> centerX, y |-> centerY]
        ELSE IF N = 2 THEN 
            IF n = 1 THEN [x |-> centerX - radius, y |-> centerY]
            ELSE [x |-> centerX + radius, y |-> centerY]
        ELSE IF N = 3 THEN 
            IF n = 1 THEN [x |-> centerX, y |-> centerY - radius]
            ELSE IF n = 2 THEN [x |-> centerX + radius, y |-> centerY + radius \div 2]
            ELSE [x |-> centerX - radius, y |-> centerY + radius \div 2]
        ELSE IF N = 4 THEN 
            IF n = 1 THEN [x |-> centerX, y |-> centerY - radius]
            ELSE IF n = 2 THEN [x |-> centerX + radius, y |-> centerY]
            ELSE IF n = 3 THEN [x |-> centerX, y |-> centerY + radius]
            ELSE [x |-> centerX - radius, y |-> centerY]
        ELSE IF N = 5 THEN 
            IF n = 1 THEN [x |-> centerX, y |-> centerY - radius]
            ELSE IF n = 2 THEN [x |-> centerX + radius - 20, y |-> centerY - radius \div 2]
            ELSE IF n = 3 THEN [x |-> centerX + radius - 40, y |-> centerY + radius \div 2]
            ELSE IF n = 4 THEN [x |-> centerX - radius + 40, y |-> centerY + radius \div 2]
            ELSE [x |-> centerX - radius + 20, y |-> centerY - radius \div 2]
        ELSE IF N = 6 THEN 
            IF n = 1 THEN [x |-> centerX, y |-> centerY - radius]
            ELSE IF n = 2 THEN [x |-> centerX + radius, y |-> centerY - radius \div 2]
            ELSE IF n = 3 THEN [x |-> centerX + radius, y |-> centerY + radius \div 2]
            ELSE IF n = 4 THEN [x |-> centerX, y |-> centerY + radius]
            ELSE IF n = 5 THEN [x |-> centerX - radius, y |-> centerY + radius \div 2]
            ELSE [x |-> centerX - radius, y |-> centerY - radius \div 2]
        ELSE \* For N > 6, use a simplified grid layout
            LET row == (n - 1) \div 3
                col == (n - 1) % 3
            IN [x |-> centerX - radius + col * radius,
                y |-> centerY - radius + row * (radius \div 2)]]

\* Node visual representation with shape-based activity indication
NodeCircles == 
    [n \in AnimNodes |-> 
        LET nodeActive == active[n-1]
            nodeColor == color[n-1]
            fillColor == IF nodeColor = "white" THEN "#f8f9fa" ELSE "#343a40"
            strokeColor == "#000000"
            strokeWidth == "2"
        IN IF nodeActive 
           THEN Circle(Coords[n].x, Coords[n].y, 25, 
                ("fill" :> fillColor @@
                 "stroke" :> strokeColor @@
                 "stroke-width" :> strokeWidth @@
                 "opacity" :> "0.9"))
           ELSE Rect(Coords[n].x - 25, Coords[n].y - 25, 50, 50,
                ("fill" :> fillColor @@
                 "stroke" :> strokeColor @@
                 "stroke-width" :> strokeWidth @@
                 "opacity" :> "0.9"))]

\* Node labels (node IDs)
NodeLabels == 
    [n \in AnimNodes |-> 
        Text(Coords[n].x, Coords[n].y + 5, ToString(n-1),
            ("fill" :> "#000000" @@
             "text-anchor" :> "middle" @@
             "font-family" :> "monospace" @@
             "font-size" :> "14" @@
             "font-weight" :> "bold"))]

\* Counter display
NodeCounters == 
    [n \in AnimNodes |-> 
        Text(Coords[n].x, Coords[n].y + 35, "C:" \o ToString(counter[n-1]),
            ("fill" :> "#0066cc" @@
             "text-anchor" :> "middle" @@
             "font-family" :> "monospace" @@
             "font-size" :> "12" @@
             "font-weight" :> "bold"))]

\* Pending messages display
NodePending == 
    [n \in AnimNodes |-> 
        Text(Coords[n].x, Coords[n].y + 50, "P:" \o ToString(pending[n-1]),
            ("fill" :> "#dc3545" @@
             "text-anchor" :> "middle" @@
             "font-family" :> "monospace" @@
             "font-size" :> "12" @@
             "font-weight" :> "bold"))]

ABS(x) == IF x >= 0 THEN x ELSE -x

\* Ring connections (arrows between nodes)
RingConnections ==
    [n \in AnimNodes |-> 
        LET nextNode == IF n = N THEN 1 ELSE n + 1
            \* Calculate offset from center of node towards next node
            dx == Coords[nextNode].x - Coords[n].x
            dy == Coords[nextNode].y - Coords[n].y
            \* Simple normalization for offset (approximate)
            dist == IF dx = 0 /\ dy = 0 THEN 1 
                    ELSE IF ABS(dx) > ABS(dy) THEN ABS(dx) 
                    ELSE ABS(dy)
            offsetX == (dx * 25) \div dist  \* 25 is node radius
            offsetY == (dy * 25) \div dist
            x1 == Coords[n].x + offsetX
            y1 == Coords[n].y + offsetY
            x2 == Coords[nextNode].x - offsetX
            y2 == Coords[nextNode].y - offsetY
        IN Line(x1, y1, x2, y2,
            ("stroke" :> "#6c757d" @@
             "stroke-width" :> "2" @@
             "opacity" :> "0.6"))]

\* Enhanced token representation
Token == 
    LET tokenPos == token.pos + 1
        tokenX == Coords[tokenPos].x
        tokenY == Coords[tokenPos].y - 15  \* Position above the node
        tokenColor == IF token.color = "white" THEN "#ffc107" ELSE "#6f42c1"
    IN <<
        \* Token circle
        Circle(tokenX, tokenY, 8, 
            ("fill" :> tokenColor @@
             "stroke" :> "#000000" @@
             "stroke-width" :> "2" @@
             "opacity" :> "1.0")),
        \* Token info
        Text(tokenX - 25, tokenY - 25, "q:" \o ToString(token.q),
            ("fill" :> "#000000" @@
             "text-anchor" :> "middle" @@
             "font-family" :> "monospace" @@
             "font-size" :> "10"))
    >>

\* Legend and status information
Legend ==
    <<
        \* Title
        Text(50, 30, "EWD998 Termination Detection",
            ("fill" :> "#000000" @@
             "font-family" :> "Arial, sans-serif" @@
             "font-size" :> "18" @@
             "font-weight" :> "bold")),
        \* Legend items
        Text(50, 55, "Active (circle) and inactive (square) node",
            ("fill" :> "#000000" @@
             "font-family" :> "Arial, sans-serif" @@
             "font-size" :> "12")),
        Text(50, 75, "Untainted (white) and tainted (black) node",
            ("fill" :> "#000000" @@
             "font-family" :> "Arial, sans-serif" @@
             "font-size" :> "12")),
        Text(50, 95, "C:n = Counter value",
            ("fill" :> "#0066cc" @@
             "font-family" :> "Arial, sans-serif" @@
             "font-size" :> "12")),
        Text(300, 55, "T = Token (yellow=white, purple=black)",
            ("fill" :> "#000000" @@
             "font-family" :> "Arial, sans-serif" @@
             "font-size" :> "12")),
        Text(300, 75, "q:n = Token queue count",
            ("fill" :> "#000000" @@
             "font-family" :> "Arial, sans-serif" @@
             "font-size" :> "12")),
        Text(300, 95, "P:n = Pending messages",
            ("fill" :> "#dc3545" @@
             "font-family" :> "Arial, sans-serif" @@
             "font-size" :> "12"))
    >>



\* Termination status indicator
TerminationStatus ==
    LET isTerminated == terminated
        \* Termination is detected when token returns to node 0 with proper conditions
        terminationDetected == /\ token.pos = 0
                               /\ token.color = "white" 
                               /\ color[0] = "white"
                               /\ counter[0] + token.q = 0
        statusText == IF terminationDetected THEN "TERM. DETECTED"
                      ELSE IF isTerminated THEN "TERMINATED" 
                      ELSE "RUNNING"
        statusColor == IF terminationDetected THEN "#28a745"
                       ELSE IF isTerminated THEN "#ffc107"
                       ELSE "#dc3545"
    IN <<
        Rect(560, 40, 160, 30,
            ("fill" :> statusColor @@
             "stroke" :> "#000000" @@
             "stroke-width" :> "2" @@
             "rx" :> "5" @@
             "opacity" :> "0.9")),
        Text(640, 60, statusText,
            ("fill" :> "#000000" @@
             "text-anchor" :> "middle" @@
             "font-family" :> "Arial, sans-serif" @@
             "font-size" :> "14" @@
             "font-weight" :> "bold"))
    >>

AnimView ==
    Group(Legend \o 
          NodeCircles \o 
          NodeLabels \o 
          NodeCounters \o 
          NodePending \o 
          RingConnections \o 
          Token \o 
          TerminationStatus, 
          ("transform" :> "translate(20 20)"))

\* Animation alias for TLC to generate SVG files
AnimAlias ==
    [ _anim |-> Serialize("<svg viewBox='0 0 800 600' xmlns='http://www.w3.org/2000/svg'>" \o 
                         SVGElemToString(AnimView) \o 
                         "</svg>", 
                         "EWD998_anim_" \o ToString(TLCGet("level")) \o ".svg",
                         [format |-> "TXT", charset |-> "UTF-8", openOptions |-> <<"WRITE", "CREATE", "TRUNCATE_EXISTING">>]) ]

=============================================================================

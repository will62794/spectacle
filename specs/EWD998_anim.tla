---- MODULE EWD998_anim ----
EXTENDS TLC, EWD998, SVG, IOUtils


\* 
\* Animation definitions.
\* 

\* SVG functions are provided by the SVG module - no need to redefine them

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

\* Animation alias for generating SVG files with TLC.
AnimAlias ==
    [
        active |-> active, pending |-> pending, color |-> color, counter |-> counter, token |-> token
    ] @@
    LET IO == INSTANCE IOUtils IN
    [ _anim |-> IO!Serialize("<svg viewBox='0 0 760 480' xmlns='http://www.w3.org/2000/svg'>" \o 
                         SVGElemToString(AnimView) \o 
                         "</svg>", 
                         "EWD998_anim_" \o ToString(TLCGet("level")) \o ".svg",
                         [format |-> "TXT", charset |-> "UTF-8", openOptions |-> <<"WRITE", "CREATE", "TRUNCATE_EXISTING">>]) ]

====

---- MODULE queue_anim ----
EXTENDS TLC, queue, SVG, Integers



\* Define basic animation elements following AbstractRaft_anim style.

\* Helper to get the number of elements in the queue
QLen == Len(q)

\* Constants for visual layout
BoxW == 40
BoxH == 40
BoxY == 30
Spacing == 5
StartX == 40

\* Render a single queue box and the corresponding value as text
QueueBox(i, val) == 
    LET x0 == StartX + (i-1) * (BoxW + Spacing) IN
    Group(<<
        Rect(x0, BoxY, BoxW, BoxH, [fill |-> "#e6f2ff", stroke |-> "black"]),
        Text(x0 + BoxW \div 2, BoxY + BoxH \div 2 + 6, ToString(val), ("text-anchor" :> "middle" @@ "font-size" :> "20px" @@ "fill" :> "black"))
    >>, [k \in {} |-> {}])

\* The queue visual as a sequence of boxes for each value in q
QueueBoxes == [i \in 1..QLen |-> QueueBox(i, q[i])]

QueueArrow == 
    \* An arrow as a polygon/line indicating enqueue direction
    LET tailX == StartX + (QLen * (BoxW + Spacing)) IN
    SVGElem("polygon", ("points" :> 
        ToString(tailX+20) \o "," \o ToString(BoxY+BoxH \div 2-7) \o " " \o
        ToString(tailX+40) \o "," \o ToString(BoxY+BoxH \div 2) \o " " \o
        ToString(tailX+20) \o "," \o ToString(BoxY+BoxH \div 2+7) @@
        "fill" :> "#3498db"), <<>>, "")

\* The complete animation view
AnimView == 
    Group(
        [i \in 1..QLen |-> QueueBoxes[i]]
        \o <<QueueArrow>>,
        [transform |-> "translate(0,0) scale(1.0)"]
    )



====
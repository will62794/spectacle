---- MODULE counter_anim ----
EXTENDS counter, Animation

Elems == <<
    Rect(50, 50, 350, 12, [fill |-> "red"]),
    Circle(xval * 50 + 80, 50, 10, [fill |-> "blue"])>>
AnimView == Group(Elems, [transform |-> "translate(40, 40) scale(1.25)"])

====
---- MODULE queue ----
EXTENDS TLC, Sequences, Naturals

CONSTANT Value
CONSTANT Capacity

\* The queue is a sequence of values.
VARIABLE q

Push(v) == 
    /\ Len(q) < Capacity
    /\ q' = q \o <<v>>

Pop == 
    /\ Len(q) > 0
    /\ q' = Tail(q)

Init == 
    /\ q = <<>>

Next ==
    \/ \E v \in Value : Push(v)
    \/ Pop

====
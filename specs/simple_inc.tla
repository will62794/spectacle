---- MODULE simple_inc ----
EXTENDS TLC, Naturals

VARIABLE x

Init ==
    x = 0

Next ==
    \/ x <= 3 /\ x' = x + 1
    \/ x = 3  /\ x' = 5
    \* Go back to zero.
    \/ x \in {4,5} /\ x' = 0


====
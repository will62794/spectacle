----------------------- MODULE simple_nums ------------------------
EXTENDS Naturals, Integers

VARIABLE x
Init == x = 1

A == x' = x + 1
B == x' = (4)

Next == 
    \/ A
    \* \/ A
    \/ B
====
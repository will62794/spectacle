----------------------- MODULE simple_inline_comment ------------------------
EXTENDS Naturals

R1 == [b |-> 3]
R2 == [a |-> 4, b |-> 3]

VARIABLE x

Init == 
    \/ x = (2 > 3 => 3 + "a" = 12)
    \/ (* inline comment *) x = (4 + 8)
    \/ 
        /\ \* test inline 2. 
           x \in {44,55}
        /\ (* test inline 3. *) x > 50

Next == x' = x 
====================
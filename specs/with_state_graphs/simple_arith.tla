----------------------- MODULE simple_arith ------------------------
EXTENDS Naturals, Integers

VARIABLE x
Init == 
    \/ (x = 1 + 2 + 4) 
    \/ (x = {1,2,3} \cap {2,3})
    \/ x = 6
    \/ x = 5 * 14
    \/ x = 8 * 3
    \/ x = 3 % 5
    \/ x = 5 % 3
    \/ x = -2 % 6
    \/ x = 12 \div 5
    \/ x = 19 \div 2
    \/ x = 24 \div 4
    \/ x = 10 \div 1
    \/ x = 2 ^ 4
    \/ x = 3 ^ 5
    \/ x = 1 ^ 0
    \/ x = 5 ^ 1
    \/ x = 6 ^ 6

Next == x' = x
====
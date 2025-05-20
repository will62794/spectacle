---- MODULE simple_definition2 ----
EXTENDS Naturals

VARIABLE x

Other(jj, arg) == jj + arg + 55
F(arg) == arg < 22
D(arg, b) == 
    LET val == Other(arg, b) IN
        val

Action1(arg) == 
    \* /\ \A v \in {5,6,7} : 
    /\ F(3)
    /\ x' = (x + arg) % 30

Init == x = 0
Next == \E arg \in {11,22} : Action1(arg) 


====
---- MODULE simple_definition2 ----
EXTENDS Naturals

VARIABLE x

Other(jj, arg) == jj + arg + 55
F(arg, c) == arg < 22
D(arg, y) == 
    LET val == Other(arg, y) IN
        val

Action1(arg) == 
    /\ \A v \in {5,6,7} : F(v, arg)
    /\ x' = (x + D(3, arg) +  arg) % 30

Init == x = 0
Next == 
    \/ x' = 100
    \/ \E arg \in {11,22} : Action1(arg) 


====
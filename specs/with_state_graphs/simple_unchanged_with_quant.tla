---- MODULE simple_unchanged_with_quant ----
EXTENDS Naturals

VARIABLE x
VARIABLE y

xvars == <<x>>
yvars == <<y>>

vars == <<xvars,yvars>>

Init == x = 0 /\ y = 1

Next == 
    \/ (\A t \in {3,4} : (x' = 5 /\ y' = y))
    \/ (\A t \in {3,4} : (t > 2 /\ x' = 16 /\ y' = 17))
    \/ (\A t \in {3,4} : (t > 2 /\ UNCHANGED vars))
====
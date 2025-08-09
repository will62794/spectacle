---- MODULE simple_tlc_fn ----
EXTENDS TLC

VARIABLES
    x,
    y

Init ==
    \/ /\ x = (0 :> 0)
       /\ y = (1 :> 1)
    \/ /\ x = 2 :> 3
       /\ y = 4 :> 5
    \/ /\ x \in [{1,2} \X {3} -> {55,66,77}] 
       /\ y = x[1,3]
    \/ /\ x \in [{1,2} \X {3} -> {55,66,77}] 
       /\ y = x[<<2,3>>]
Next == UNCHANGED <<x, y>>

====
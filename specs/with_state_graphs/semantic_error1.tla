---- MODULE semantic_error1 ----
EXTENDS TLC, Naturals

VARIABLE x,y

Init == x = 0 /\ y = 0

Action1 == 
    \E s,t \in {3,4} : 
        /\ x' = x \cup {s+t} 
        /\ y' = y

Action2 == 
    \E s,t \in {3,4} : 
        /\ x' = (x + s + t) % 8 
        /\ y' = y

Next == 
    \/ Action1
    \/ Action2

====
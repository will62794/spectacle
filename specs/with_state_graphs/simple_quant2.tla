----------------------- MODULE simple_quant2 ------------------------
EXTENDS Naturals

VARIABLE x

S == {1,5}
T == {2,6}
Init == 
    \/ \E c \in SUBSET {0,1} : c # {} /\ x = [i \in {"a"} |-> c]
    \/ \E c,d \in S, h,k \in {5,6} : x = c + d + h + k
    \/ \E <<q,z>> \in S \X T, h,k \in {5,6} : x = q + z + h + k

Next == x' = x 
====
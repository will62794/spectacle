---- MODULE simple_disjunction_init ----
EXTENDS Naturals

\* Test a variety of disjunctions (e.g. \/, \E, \in, etc.) 
\* in initial state generation.

VARIABLE x

Init == 
    \/ (x = 0 \/ x = 1 \/ FALSE)
    \/ x = 2
    \/ FALSE
    \/ x \in {4,5,6}
    \/ x \in {12,13}
    \/ x \in {14,15,16} /\ x \notin {16,17}
    \/ x \in {14,15} /\ x \notin {15}  
    \/ x \in {14,15} /\ (~(\E a \in {15} : x = a)) 
    \/ \E i \in {1,2,3} : x = i \/ (x = i + 6)
    \/ \E k \in {1,2,3} : k = 5
    \/ x \in {7,8,9,10} /\ x \notin {11,10}  
    \/ x \in {7,8,9,10} /\ x \notin {10,11}  

    
Next == 
    /\ x' = x

====
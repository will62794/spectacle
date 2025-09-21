---- MODULE simple_disjunction_constant ----

\* Test a variety of disjunctions (e.g. \/, \E, \in, etc.) in constant expressions.

VARIABLE x

Init == 
    /\ x = [
            exists1 |-> \E i \in {1,2,3} : i = 2,
            exists2 |-> \E i \in {1,2,3} : \E j \in {4,5,6} : i = 0 \/ j = 4,
            exists3 |-> \E i \in {1,2,3} , j \in {4,5,6} : i = 0 \/ j = 4,
            exists4 |-> \E i,j \in {1,2,3} : i = 0 /\ j = 2,
            exists5 |-> \E i,j \in {1,2,3}, u,v,t \in {4,5} : i = 0 /\ j = 2 /\ u = 4 /\ v = 6,
            existsmultiline |-> (
                \E vari \in {1,2},
                   varj \in {3,4} : vari = 0 /\ varj = 2),
            notexists1 |-> ~(\E a \in {15,16,17} : a = 18),
            notexists2 |-> ~(\E a \in {15,16,17} : a = 16),
            setin1 |-> 1 \in {2,3},
            setin2 |-> 2 \in {2,3},
            setnotin1 |-> 2 \notin {3,2},
            setnotin2 |-> 4 \notin {2,3},
            disj1 |-> (1 \in {2,3}) \/ (2 \in {2,3}),
            disj2 |-> FALSE \/ TRUE,
            disjlist1 |-> (
                \/ TRUE
                \/ FALSE
            ),
            disjlist2 |-> (
                \/ 1 \in {2,3}
                \/ FALSE
            ),
            bottom |-> FALSE
        ]  

Next == x' = x

====
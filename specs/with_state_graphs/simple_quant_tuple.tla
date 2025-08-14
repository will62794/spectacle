---- MODULE simple_quant_tuple ----
EXTENDS Naturals
\* See https://github.com/will62794/tla-web/issues/17.

VARIABLE x, y

Init == 
    /\ x = 0
    /\ y = 0

Next == 
    \/ \E <<i,j>> \in {<<1,2>>,<<3,4>>}:
    	    /\ x' = i
            /\ y' = j
    \/ \E <<i,j>> \in {<<1,2>>,<<3,4>>} : \E <<n,m>> \in {<<15,16>>,<<17,18>>} :
    	/\ x' = i + m
        /\ y' = j + n
    \* Enable once this is handled correctly.
    \* \/ \E <<i,j>> \in {<<1,2>>,<<3,4>>}, <<n,m>> \in {<<25,16>>,<<27,18>>} :
    \* 	/\ x' = i + m
    \*     /\ y' = j + n
====
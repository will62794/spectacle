----------------------- MODULE simple_implies ------------------------
EXTENDS Naturals

R1 == [b |-> 3]
R2 == [a |-> 4, b |-> 3]

VARIABLE x

Init == 
    (* initial comment *)
    \/ x = (3 > 2 => FALSE)
    \* Test short-circuiting avoids evaluation of expressions that would throw error.
    \/ x = (2 > 3 => 3 + "a" = 12)
    \/ x = (("a" \in DOMAIN R1) => R1["a"] = 4)
    (* 
     test comment 
    *)
    \/ x = (("a" \in DOMAIN R2) => R2["a"] = 4)
    \/ x = (\E r \in {R1, R2} : "a" \in DOMAIN r => r["a"] = 4)
    \* Test bi-directional implication (iff)
    \/ x = (3 > 2 <=> 2 < 3)
    \/ x = (3 > 2 <=> 4 > 2)

Next == x' = x 
====================
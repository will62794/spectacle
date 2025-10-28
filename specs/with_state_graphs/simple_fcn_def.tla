---- MODULE simple_fcn_def ----
EXTENDS Naturals, TLC

VARIABLE x

\* Function definition.
f2[a,b \in {1,3}, c \in {6,9}] == a + b + c
f4[a \in {1,3}] == a + a

fact[a \in {1,2,3,4}] == IF a = 1 THEN 1 ELSE a * fact[a-1]
sum[a \in {1,2,3,4}] == IF a = 1 THEN 1 ELSE a + sum[a-1]

N == 3
sc[<<a, b>> \in (0 .. N + 1) \X (8 .. 12)] == a + b

Init == 
    \/ x = ([
            e |-> f2[3,1,9],
            d |-> f4[3],
            f |-> fact[3],
            g |-> sum[4]
        ])
    \/ x = f2
    \* \/ x = sc
    

Next == x' = x

====
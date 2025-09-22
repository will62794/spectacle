----------------------- MODULE simple_inline_comment_constant ------------------------
EXTENDS Naturals

R1 == [b |-> 3]
R2 == [a |-> 4, b |-> 3]

CONSTANT 
    C , (** something **)
    D (** something else **)

VARIABLE x

Init == 
    \/ x = C + 12 + D

Next == x' = x 
====================
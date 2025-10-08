----------------------- MODULE simple_seq ------------------------
EXTENDS Sequences,TLC, Naturals
VARIABLE x
Init == 
    \/ x = [
            seqlen |-> Len(<<1,2,3>>),
            head1 |-> Head(<<1,2,3>>),
            head2 |-> Head(<<3,2,1>>),
            tail1 |-> Tail(<<1,2,3>>),
            tail2 |-> Tail(<<1>>),
            append1 |-> Append(<<1>>, 2),
            append2 |-> Append(<<1,2,3>>, 4),
            append3 |-> Append(<<>>, 2),
            append4 |-> { Append(<<1>>, c) : c \in {2,3,4} },
            concat1 |-> <<1,2>> \o <<3,4>>,
            concat2 |-> <<>> \o <<3,4,5,6>>,
            concat3 |-> (1 :> 12) \o <<3,4,5,6>>,
            concat4 |-> (2 :> 12 @@ 1 :> 13) \o <<3,4,5,6>>,
            concat5 |-> (3 :> 12 @@ 1 :> 13 @@ 2 :> 78 @@ 4 :> 9) \o <<3,4,5,6>>,
            domain1 |-> DOMAIN [a |-> 1, b |-> 2, c |-> 3],
            domain2 |-> DOMAIN <<1,2,3>>,
            domain3 |-> DOMAIN <<>>,
            get1 |-> <<1,2,3>>[1],
            get2 |-> <<1,2,3>>[2],
            get3 |-> <<1,2,3>>[3],
            eq1 |-> <<1,2,3>> = <<1,2,3>>,
            eq2 |-> <<1,2,3>> = <<1,2,4>>,
            eq3 |-> <<1,2,3>> = <<1,2,4,5>>,
            eq4 |-> SelectSeq(<<1,2,3,4>>, LAMBDA v: v < 3),
            eq5 |-> SelectSeq(<<1,2,3,4>>, LAMBDA v: v > 2),
            eq6 |-> SelectSeq(<<1,2,3,4>>, LAMBDA v: v = 2),
            eq7 |-> SelectSeq(<<1,2,3,4>>, LAMBDA v: v > 10)
        ]
    \/ x = SubSeq(<<1,2,3,4,5,6,7,8>>, 2,5)
    \/ x = SubSeq(<<1,2,3,4,5,6,7,8>>, 1+2,5)
    \/ x = SortSeq(<<9,4,3,6,1,25,66,22>>, LAMBDA a,b: a < b)
    \/ x = SortSeq(<<5,4,3,2,1,66,77,101,99,88>>, LAMBDA a,b: a < b)
    \/ x = SortSeq(<<5,4,3,2,1,66,77,101,96,88>>, LAMBDA a,b: a > b)
Next == x' = x
====
---- MODULE empty_domain_and_seq ----
EXTENDS TLC, Sequences

VARIABLE x

Init == 
    \/ x = ([a \in {} |-> {}] # <<>>)
    \/ x = ([a \in {} |-> {}] \o <<12>>)
    \/ x = Len([a \in {} |-> {}])
    \/ x = Append([a \in {} |-> {}], 55)
    \/ x = DOMAIN [a \in {} |-> {}] \cup {66}

Next == x' = x

====
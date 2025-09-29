---------------------------- MODULE DiningPhilosophers ----------------------------

EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANT N \* Number of philosophers
ASSUME N \in Nat \ {0}

P == 1..N

VARIABLES philosophers, forks
vars == <<philosophers, forks>>

TypeOK ==
    /\ philosophers \in [P -> SUBSET P]
    /\ forks \in SUBSET P

Init ==
    \* each philosopher starts with no forks
    /\ philosophers = [ p \in P |-> {} ]
    \* all forks are available
    /\ forks = 1..N

TakeLeft(p) ==
    LET rightFork == ((p + 1) % (N+1)) 
        leftFork == p IN
    \* p # 1 grabs the right fork first.
    \* /\ p # 1 => philosophers[p] = {rightFork}
    /\ leftFork \in forks
    /\ forks' = forks \ {leftFork}
    /\ philosophers' = 
        [philosophers EXCEPT ![p] = philosophers[p] \cup {leftFork}]

TakeRight(p) ==
    LET rightFork == ((p + 1) % (N+1)) 
        leftFork == p IN
    \* First philosopher to grab the left fork first.
    \* /\ p = 1 => philosophers[p] = {leftFork}
    /\ rightFork \in forks 
    /\ forks' = forks \ {rightFork}
    /\ philosophers' = 
        [philosophers EXCEPT ![p] = philosophers[p] \cup {rightFork}]

Release(p) ==
    LET rightFork == ((p + 1) % (N+1)) 
        leftFork == p IN
    /\ philosophers[p] = {leftFork, rightFork}
    /\ forks' = forks \cup {leftFork, rightFork}
    /\ philosophers' = [philosophers EXCEPT ![p] = {}]

Next ==
    \/ \E p \in P:
        \/ TakeLeft(p)
        \/ TakeRight(p)
        \/ Release(p)

Spec ==
    Init /\ [][Next]_vars /\ WF_vars(Next)

IsEating(p) ==
    Cardinality(philosophers[p]) = 2

NoStarvation ==
    \A p \in P: []<>IsEating(p)

-----

Alias ==
    LET ThinkHungryEat(p) ==
        IF IsEating(p) THEN "eating"
        ELSE IF Cardinality(philosophers[p]) = 1 THEN "hungry"
        ELSE "thinking" IN
    [
        philosophers |-> philosophers,
        forks |-> forks,
        eating |-> [ p \in DOMAIN philosophers |-> ThinkHungryEat(p) ]
    ]

-----------------------------------------------------------------------------


=====

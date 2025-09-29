------------------------- MODULE CabbageGoatWolf -----------------------------
EXTENDS Naturals, FiniteSets, TLC, Sequences
\* Solving the https://en.wikipedia.org/wiki/Wolf,_goat_and_cabbage_problem
\* Modified from https://github.com/muratdem/PlusCal-examples/blob/master/Puzzles/CabbageGoatWolf_Pluscal.tla
    
Sides == {1,2}
C == "Cabbage"
G == "Goat"
W == "Wolf"
F == "Farmer"

Allowed(S) == 
    \/ F \in S 
    \/ (/\ ~ ( C \in S  /\  G \in S )
        /\ ~ ( G \in S  /\  W \in S ) )

VARIABLES banks, boat

(* define statement *)
SafeBoats(s) ==
    { B \in SUBSET banks[s]:
        /\ F \in B
        /\ Cardinality(B) <= 2
        /\ Allowed(banks[s] \ B) }

TypeOK ==
    /\ Cardinality(banks[1]) + Cardinality(banks[2]) + Cardinality(boat) = 4
    /\ Cardinality(boat) <=2
    /\ boat \in SUBSET {F,C,G,W}
    /\ banks[1] \in SUBSET {F,C,G,W}
    /\ banks[2] \in SUBSET {F,C,G,W}

NotSolved == Cardinality(banks[2]) < 4


vars == << banks, boat >>

ProcSet == (Sides)

Init == (* Global variables *)
        /\ banks = << {C,G,W,F}, {} >>
        /\ boat = {}

LoadBoat(self, P) == 
    /\ (banks[self]#{} /\  boat={})
    /\ boat' = P
    /\ banks' = [banks EXCEPT ![self] = banks[self] \ P]

EmptyBoat(self) == 
    /\ (boat#{})
    /\ banks' = [banks EXCEPT ![self] = banks[self] \union boat]
    /\ boat' = {}

Next == 
    \/ \E self \in Sides: EmptyBoat(self)
    \/ \E self \in Sides : \E P \in SafeBoats(self): LoadBoat(self, P)

Spec == Init /\ [][Next]_vars



============================================================

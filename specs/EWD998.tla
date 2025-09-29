------------------------------- MODULE EWD998 -------------------------------
EXTENDS Integers, TLC, Sequences

CONSTANT N

Node == 0 .. N-1

Color == {"white", "black"}

VARIABLES 
    active,
    pending,
    color,
    counter,
    token

vars == <<active, pending, color, counter, token>>

TypeOK ==
    /\ active \in [Node -> BOOLEAN]
    /\ pending \in [Node -> Nat]
    /\ color \in [Node -> Color]
    /\ counter \in [Node -> Int]
    /\ token \in [ pos: Node, q: Int, color: Color ]

-----------------------------------------------------------------------------

Init ==
    /\ active \in [Node -> BOOLEAN]
    /\ pending = [i \in Node |-> 0]
    (* Rule 0 *)
    /\ color \in [Node -> Color]
    /\ counter = [i \in Node |-> 0]
    \* TODO: Address bug with repeated assignment here.
    \* /\ pending = [i \in Node |-> 0]
    /\ token = [pos |-> 0, q |-> 0, color |-> "black"]

-----------------------------------------------------------------------------

InitiateProbe ==
    (* Rules 1 + 5 + 6 *)
    /\ token.pos = 0
    /\ \* previous round inconclusive:
        \/ token.color = "black"
        \/ color[0] = "black"
        \/ counter[0] + token.q > 0
    /\ token' = [ pos |-> N-1, q |-> 0, color |-> "white"]
    /\ color' = [ color EXCEPT ![0] = "white" ]
    /\ UNCHANGED <<active, counter, pending>>                            

PassToken(i) ==
    (* Rules 2 + 4 + 7 *)
    /\ ~ active[i]
    /\ token.pos = i
    \* Rule 2 + 4
    /\ token' = [ pos |-> token["pos"] - 1, 
                    q |-> token["q"] + counter[i],
                color |-> IF color[i] = "black" THEN "black" ELSE token["color"] ]
    \* Rule 7
    /\ color' = [ color EXCEPT ![i] = "white" ]
    /\ UNCHANGED <<active, pending, counter>>

System ==
    \/ InitiateProbe
    \/ \E i \in Node \ {0}: PassToken(i)

-----------------------------------------------------------------------------

SendMsg(i, recv) ==
    /\ active[i]
    /\ counter' = [counter EXCEPT ![i] = @ + 1]
    /\ pending' = [pending EXCEPT ![recv] = @ + 1]
    /\ UNCHANGED <<active, color, token>>

\* Wakeup(i) in AsyncTerminationDetection.
RecvMsg(i) ==
    /\ pending[i] > 0
    /\ active' = [active EXCEPT ![i] = TRUE]
    /\ pending' = [pending EXCEPT ![i] = @ - 1]
    /\ counter' = [counter EXCEPT ![i] = @ - 1]
    /\ color' = [ color EXCEPT ![i] = "black" ]
    /\ UNCHANGED <<token>>

\* Terminate(i) in AsyncTerminationDetection.
Deactivate(i) ==
    /\ active[i]
    \* * ...in the next state (the prime operator ').
    \* * The previous expression didn't say anything about the other values of the
     \* * function, or even state that active' is a function (function update).
    /\ active' = [ active EXCEPT ![i] = FALSE ]
    \*/\ active' \in { f \in [ Node -> BOOLEAN] : \A n \in Node: ~active[n] => ~f[n] }
    \*//\ active' # active
    /\ UNCHANGED <<pending, color, counter, token>>

\* Environment == 
\*     \E n \in Node:
\*         \/ SendMsg(n)
\*         \/ RecvMsg(n)
\*         \/ Deactivate(n)

-----------------------------------------------------------------------------

\* Next ==
\*   \/ System 
\*   \/ Environment

Next ==
  \/ InitiateProbe
  \/ \E i \in Node \ {0} : PassToken(i)
  \/ \E n \in Node :  \E recv \in (Node \ {n}) : SendMsg(n, recv)
  \/ \E n \in Node : RecvMsg(n)
  \/ \E n \in Node : Deactivate(n)

Spec == Init /\ [][Next]_vars /\ WF_vars(System)

-----------------------------------------------------------------------------

terminated ==
    \A n \in Node : ~active[n] /\ pending[n] = 0

-----------------------------------------------------------------------------


=============================================================================

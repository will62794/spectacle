\*34567890123456789012345678901234567890123456789012
source: https://raw.githubusercontent.com/lucformalmethodscourse/microwave-tla/refs/heads/main/Microwave.cfg

-------------------------- MODULE Microwave  --------------------------

EXTENDS TLC, Integers

CONSTANTS
  \* Flag for enabling safety check upon starting radiation
  ImplementStartSafety,
  \* Flag for enabling safety check upon opening door
  ImplementOpenDoorSafety

VARIABLES
  \* See TypeOK below for type constraints
  door,
  radiation,
  timeRemaining

\* Tuple of all variables
vars == << door, radiation, timeRemaining >>

\* Symbolic names for significant strings
OFF == "off"
ON == "on"
CLOSED == "closed"
OPEN == "open"

\* Dynamic type invariant
TypeOK == 
  /\ door \in { CLOSED, OPEN }
  /\ radiation \in { OFF, ON }
  /\ timeRemaining \in Nat

MaxTime == 30

\* Valid initial state(s)
Init ==
  /\ door \in { OPEN, CLOSED }
  /\ radiation = OFF
  /\ timeRemaining = 0

\* Increment remaining time by one second
IncTime ==
  /\ radiation = OFF
  /\ timeRemaining' = timeRemaining + 1
  /\ timeRemaining' <= MaxTime
  /\ UNCHANGED << door, radiation >>

\* Start radiation and time countdown
Start ==
  /\ radiation = OFF
  /\ ImplementStartSafety => door = CLOSED
  /\ timeRemaining > 0
  /\ radiation' = ON
  /\ UNCHANGED << door, timeRemaining >>

\* Cancel radiation and reset remaining time
Cancel ==
  /\ radiation' = OFF
  /\ timeRemaining' = 0
  /\ UNCHANGED << door >>

\* Internal clock tick for time countdown
Tick ==
  /\ radiation = ON
  /\ timeRemaining' = timeRemaining - 1
  /\ timeRemaining' >= 0
  /\ IF timeRemaining' = 0 
     THEN radiation' = OFF 
     ELSE UNCHANGED << radiation >>
  /\ UNCHANGED << door >>

\* Open door
OpenDoor ==
  /\ door' = OPEN
  /\ IF ImplementOpenDoorSafety 
     THEN radiation' = OFF 
     ELSE UNCHANGED << radiation >>
  /\ UNCHANGED << timeRemaining >>

\* Close door
CloseDoor ==
  /\ door' = CLOSED
  /\ UNCHANGED << radiation, timeRemaining >>

\* All valid actions (state transitions)
Next ==
  \/ IncTime
  \/ Start
  \/ Cancel
  \/ OpenDoor
  \/ CloseDoor
  \/ Tick

\* All valid system behaviors starting from the initial state
Spec == Init /\ [][Next]_vars

\* Valid system behaviors with weak fairness to disallow stuttering
FSpec == Spec /\ WF_vars(Tick)

\* Safety check to detect radiation with door open
DoorSafety == door = OPEN => radiation = OFF

\* Temporal check to detect indefinite radiation
HeatLiveness == radiation = ON ~> radiation = OFF

RunsUntilDoneOrInterrupted == 
  [][radiation = ON => radiation' = ON \/ timeRemaining' = 0 \/ door' = OPEN]_vars

====

(* other possible events
    action := "10min"
    action := "1min"
    action := "10sec"
    action := "power"
    action := "timer"
*)

\* DoorSafety == RequireSafety => radiation = ON => door = CLOSED

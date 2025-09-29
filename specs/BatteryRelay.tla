
## Battery Relay: Can You Help The Valets?

Four vehicles are stranded in a parking garage with dead batteries, and all of the charging
stations are currently occupied. It's nearly 4:45 PM, and their owners are eager to head home
at 5pm.

Thankfully, the valets have a spare battery—just enough to jump-start one vehicle and drive it
to another garage, where a fleet charger can instantly recharge all four vehicles at once.
The catch? It's all or nothing: the charger only works if all four vehicles are plugged in at
the same time.

There's not enough time to shuttle each vehicle one by one. However, the valets can tow a
second vehicle behind a running one—but only if the towing vehicle is large enough. A smaller
vehicle can't tow a larger one.

Can you figure out the best way for the valets to move all four vehicles to the other garage
in a single trip?

-------------------------------- MODULE BatteryRelay --------------------------------
EXTENDS Naturals, FiniteSets, TLC, Sequences

CONSTANT MaxLevel
ASSUME MaxLevel \in Nat

CONSTANT Cost
ASSUME 
    /\ DOMAIN Cost \in SUBSET STRING
    /\ \A n \in DOMAIN Cost: Cost[n] \in Nat

MyCost == [
    Truck |-> 10,
    Car   |-> 5,
    Bike  |-> 2,
    Scooter |-> 1
]

VARIABLES left, right, batteryLeft, batteryLevel
vars == <<left, right, batteryLeft, batteryLevel>>

Vehicles == DOMAIN Cost

TypeOK ==
    /\ left \subseteq Vehicles
    /\ right \subseteq Vehicles
    /\ batteryLeft \in BOOLEAN 
    /\ batteryLevel \in Nat

(* Initial state: all Vehicles and the battery are on the left side.
   The spare battery is fully charged.   *)
Init ==
    /\ left = Vehicles
    /\ right = {}
    /\ batteryLeft = TRUE
    /\ batteryLevel = MaxLevel

(* Action: from one or two vehicles left to right *)
LeftToRight(group, cost) ==
    (* Before the move: *)
    (* The group must be non-empty and contain at most two vehicles *)
    /\ Cardinality(group) \in 1..2
    (* Can only move vehicles to the right that are on the left side *)
    /\ group \in SUBSET left
    (* The battery has to be left *)
    /\ batteryLeft = TRUE
    (* After the move: *)
    (* The battery will be on the right side *)
    /\ batteryLeft' = ~batteryLeft
    (* The group of vehicles will be removed from the left side *)
    /\ left' = left \ group
    (* The group of vehicles will be added to the right side *)
    /\ right' = right \union group
    (* The battery will be decreased by the cost of moving the 
       biggest vehicle of the group *)
    /\ batteryLevel' = batteryLevel - cost

(* Action: from right to left *)
RightToLeft(group, cost) ==
    /\ Cardinality(group) \in 1..2
    /\ group \in SUBSET right
    /\ batteryLeft = FALSE
    /\ batteryLeft' = ~batteryLeft
    /\ right' = right \ group
    /\ left' = left \union group
    /\ batteryLevel' = batteryLevel - cost

Max(S) ==
    CHOOSE e \in S: \A x \in S: e >= x

(* Next-state relation *)
Next ==
    \/ \E group \in (SUBSET Vehicles) \ {{}} :
        \E c \in {Max({ Cost[g] : g \in group })} :
            LeftToRight(group, c)
    \/ \E group \in (SUBSET Vehicles) \ {{}} :
        \E c \in {Max({ Cost[g] : g \in group })} :
            RightToLeft(group, c)

(* Safety: Vehicles cannot be on both sides and don't disappear or duplicate *)
Safety ==
    /\ left \intersect right = {}
    /\ left \union right = Vehicles

(* All Vehicles are on the right side and the battery is not depleted *)
Solution ==
    /\ right = Vehicles
    /\ batteryLevel >= 0

(* This invariant will be violated when we find a solution *)
NoSolution ==
    ~Solution

(* Specification *)
Spec == 
    Init /\ [][Next]_vars







====

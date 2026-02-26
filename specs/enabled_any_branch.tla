---- MODULE enabled_any_branch ----
EXTENDS Naturals

VARIABLE x

Init == x = 0

Action ==
    \/ /\ x = 1
       /\ x' = 1
    \/ /\ x = 0
       /\ x' = 1

Next ==
    /\ ENABLED Action
    /\ x' = 2

====
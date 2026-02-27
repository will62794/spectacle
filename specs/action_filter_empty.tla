---- MODULE action_filter_empty ----
EXTENDS Naturals

VARIABLE x

Init == x = 0

ActionDisabled ==
    /\ x = 1
    /\ x' = 2

ActionEnabled ==
    /\ x = 0
    /\ x' = 2

Next == ActionDisabled \/ ActionEnabled

====
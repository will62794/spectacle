---- MODULE evalLand_empty_branch_context_regression ----

CONSTANT Txn
VARIABLES validated, localReadOk

ValidateTx(txn) == txn \in validated
ReadMemLocal(txn) == txn \in localReadOk

\* Regression intent: these two guards should be equivalent.
GuardViaNegation(txn) == /\ ReadMemLocal(txn)
			 /\ ~ValidateTx(txn)

GuardViaEqFalse(txn) == /\ ReadMemLocal(txn)
			/\ ValidateTx(txn) = FALSE

NegationEquiv == \A txn \in Txn : GuardViaNegation(txn) = GuardViaEqFalse(txn)

Init == /\ validated = {}
	/\ localReadOk = {}

Next == /\ validated' = validated
	/\ localReadOk' = localReadOk

====

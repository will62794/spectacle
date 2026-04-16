---- MODULE evalUserBoundOp_instance_substitutions_regression ----

CONSTANT Txn
VARIABLES visibleTxns, validatedTxns

OpBody(p) == p \in visibleTxns

\* This wrapper models evaluating a user-bound op after applying substitution context.
ApplyWithSubstitutions(arg) == OpBody(arg)

ValidateTx(txn) == /\ txn \in Txn
		   /\ ApplyWithSubstitutions(txn)

CanUseInstanceSubst == \A txn \in Txn :
    ValidateTx(txn) = (txn \in Txn /\ txn \in visibleTxns)

Init == /\ visibleTxns = {}
	/\ validatedTxns = {}

Next == /\ visibleTxns' = visibleTxns
	/\ validatedTxns' = validatedTxns

====

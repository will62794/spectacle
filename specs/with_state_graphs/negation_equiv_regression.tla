---- MODULE negation_equiv_regression ----

VARIABLE x

ValidateTx(txn) == txn \in {1}
NegForm(txn) == ~ValidateTx(txn)
EqFalseForm(txn) == ValidateTx(txn) = FALSE

====

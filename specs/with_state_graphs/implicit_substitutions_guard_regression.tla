---------------------------------- MODULE implicit_substitutions_guard_regression -----------------------------------
EXTENDS Sequences, Integers, TLC

CONSTANTS Key, NoVal, BlockSize

Storage == [k \in Key |-> 0]
VARIABLE mem

\* explicit self-substitutions Storage <- Storage and mem <- mem should not be required.
\* Val is explicit, Storage/mem must be implicitly identity-substituted.
INSTANCE implicit_substitutions_guard_base WITH Val <- 0..BlockSize

================================================================================

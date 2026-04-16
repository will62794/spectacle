---------------------------------- MODULE Tx -----------------------------------
EXTENDS Sequences, Integers, TLC

CONSTANTS Key, NoVal, BlockSize

Storage == [k \in Key |-> 0]
VARIABLE mem

INSTANCE Mem WITH Val <- 0..BlockSize

================================================================================

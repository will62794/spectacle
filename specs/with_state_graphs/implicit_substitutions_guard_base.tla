------------------------------- MODULE implicit_substitutions_guard_base --------------------------------
EXTENDS Sequences, Integers

CONSTANTS Key, Val, NoVal, BlockSize, Storage
VARIABLE mem

\* Storage and mem should be implicitly resolved from the instantiating module.
TxIndex == 1..BlockSize
TypeOKMem == mem \in [TxIndex -> [Key -> Val]]

UseStorage == Storage
UseMem == mem

================================================================================

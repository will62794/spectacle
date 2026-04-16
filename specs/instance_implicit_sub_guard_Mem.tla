------------------------------- MODULE Mem --------------------------------
EXTENDS Sequences, Integers

CONSTANTS Key, Val, NoVal, BlockSize, Storage
VARIABLE mem

TxIndex == 1..BlockSize
TypeOKMem == mem \in [TxIndex -> [Key -> Val]]

UseStorage == Storage
UseMem == mem

================================================================================

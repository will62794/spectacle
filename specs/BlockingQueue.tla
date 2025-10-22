--------------------------- MODULE BlockingQueue ---------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* Please see https://github.com/lemmy/BlockingQueue for the original spec.

CONSTANTS Producers,   (* the (nonempty) set of producers                       *)
          Consumers,   (* the (nonempty) set of consumers                       *)
          BufCapacity  (* the maximum number of messages in the bounded buffer  *)

ASSUME Assumption ==
       /\ Producers # {}                      (* at least one producer *)
       /\ Consumers # {}                      (* at least one consumer *)
       /\ Producers \intersect Consumers = {} (* no thread is both consumer and producer *)
       /\ BufCapacity \in (Nat \ {0})         (* buffer capacity is at least 1 *)

-----------------------------------------------------------------------------

VARIABLES buffer, waitSet
vars == <<buffer, waitSet>>

RunningThreads == (Producers \cup Consumers) \ waitSet

Notify ==
    IF waitSet # {}
    THEN \E t \in waitSet : waitSet' = waitSet \ {t}
    ELSE UNCHANGED waitSet

NotifyAll ==
    waitSet' = {}

NotifyOther(Others) == 
    Notify
    \* IF waitSet \cap Others # {}
    \* THEN \E t \in waitSet \cap Others : waitSet' = waitSet \ {t}
    \* ELSE UNCHANGED waitSet

Wait(t) == /\ waitSet' = waitSet \cup {t}
           /\ UNCHANGED <<buffer>>
           
-----------------------------------------------------------------------------

Put(t, d) ==
/\ t \notin waitSet
/\ \/ /\ Len(buffer) < BufCapacity
      /\ buffer' = Append(buffer, d)
      /\ NotifyOther(Consumers)
   \/ /\ Len(buffer) = BufCapacity
      /\ Wait(t)
      
Get(t) ==
/\ t \notin waitSet
/\ \/ /\ buffer # <<>>
      /\ buffer' = Tail(buffer)
      /\ NotifyOther(Producers)
   \/ /\ buffer = <<>>
      /\ Wait(t)

-----------------------------------------------------------------------------

(* Initially, the buffer is empty and no thread is waiting. *)
Init == /\ buffer = <<>>
        /\ waitSet = {}

(* Then, pick a thread out of all running threads and have it do its thing. *)
Next == \/ \E p \in Producers: Put(p, p) \* Add some data to buffer
        \/ \E c \in Consumers: Get(c)

Spec == Init /\ [][Next]_vars
 
=============================================================================

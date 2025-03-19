--------------------------- MODULE BlockingQueue ---------------------------
EXTENDS Naturals, Sequences, FiniteSets

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

-----------------------------------------------------------------------------

\*
\*
\* Animation stuff
 \* Merge two records
 Merge(r1, r2) == 
     LET D1 == DOMAIN r1 D2 == DOMAIN r2 IN
     [k \in (D1 \cup D2) |-> IF k \in D1 THEN r1[k] ELSE r2[k]]
 
 SVGElem(_name, _attrs, _children, _innerText) == [name |-> _name, attrs |-> _attrs, children |-> _children, innerText |-> _innerText ]
 
 Text(x, y, text, attrs) == 
     (**************************************************************************)
     (* Text element.'x' and 'y' should be given as integers, and 'text' given *)
     (* as a string.                                                           *)
     (**************************************************************************)
     LET svgAttrs == [x |-> x, 
                      y |-> y] IN
     SVGElem("text", Merge(svgAttrs, attrs), <<>>, text) 
 
 \* Circle element. 'cx', 'cy', and 'r' should be given as integers.
 Circle(cx, cy, r, attrs) == 
     LET svgAttrs == [cx |-> cx, 
                      cy |-> cy, 
                      r  |-> r] IN
     SVGElem("circle", Merge(svgAttrs, attrs), <<>>, "")
 
 \* Rectangle element. 'x', 'y', 'w', and 'h' should be given as integers.
 Rect(x, y, w, h, attrs) == 
     LET svgAttrs == [x      |-> x, 
                      y      |-> y, 
                      width  |-> w, 
                      height |-> h] IN
     SVGElem("rect", Merge(svgAttrs, attrs), <<>>, "")
 
 \* Group element. 'children' is as a sequence of elements that will be contained in this group.
 Group(children, attrs) == SVGElem("g", attrs, children, "")
 
 Injective(f) == \A x, y \in DOMAIN f : f[x] = f[y] => x = y
 
 SetToSeq(S) == CHOOSE f \in [1..Cardinality(S) -> S] : Injective(f)
 
\*  Empty == [a \in {} |-> {}] \* Cannot be <<>>, which is certainly a bug in Spectacle!!!

 \* Fix to the above issued in https://github.com/will62794/spectacle/commit/f84efe7
 Empty == <<>>
 
 \* The element of buffer at index i or empty string if i is out-of-bounds.
 ElemAt(i) == 
     IF i > Len(buffer) THEN "" ELSE buffer[i]
 
 --------------------------------
 
 BufferCellColor(i) == 
     IF ElemAt(i) = "" THEN "lightgray" ELSE "lightblue"
 
 BPos == [w |-> 45]
 Pos == [ x |-> 5, y |-> 25, r |-> 20 ]
 
 BufferCell(i) == 
     LET value == Text((BPos.w + Pos.x) + 13, i * (Pos.y + 30) + 25, ElemAt(i), Empty)
         rect  == Rect((BPos.w + Pos.x), i * (Pos.y + 30), BPos.w, BPos.w, [fill |-> BufferCellColor(i)])
     IN Group(<<rect, value>>, ("transform" :> "translate(0 -25)"))
 
 Buffer == [i \in 1..BufCapacity |-> BufferCell(i)]
 
 --------------------------------
 
 CircleColor(t) == 
     IF t \in waitSet 
     THEN "red"
     ELSE "yellow"
 
 ConsSeq == SetToSeq(Consumers)
 
 ConsumerCell(i) == 
     Group(<<Circle(Pos.x, i * (Pos.y + 30), Pos.r, [fill |-> CircleColor(ConsSeq[i])]),
             Text(Pos.x - 8,   i * (Pos.y + 30) + 5, (ConsSeq[i]), Empty)
           >>, ("transform" :> "translate(135 0)"))
 
 Cons == [i \in 1..Cardinality(Consumers) |-> ConsumerCell(i)]
 
 --------------------------------
 
 ProdSeq == SetToSeq(Producers)
 
 ProdCell(i) == 
     Group(<<Circle(Pos.x, i * (Pos.y + 30), Pos.r, [fill |-> CircleColor(ProdSeq[i])]),
             Text(Pos.x - 8,   i * (Pos.y + 30) + 5, (ProdSeq[i]), Empty)
           >>, Empty)
 
 Prod == [i \in 1..Cardinality(Producers) |-> ProdCell(i)]
 
 AnimView == 
     Group(Prod \o Buffer \o Cons, 
         ("transform" :> "scale(0.75) translate(60 -50)"))
 
=============================================================================

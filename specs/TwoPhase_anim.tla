------------------------------- MODULE TwoPhase_anim ----------------------------- 
EXTENDS TLC, Naturals, Sequences, FiniteSets

(***************************************************************************)
(* This specification describes the Two-Phase Commit protocol, in which a  *)
(* transaction manager (TM) coordinates the resource managers (RMs) to     *)
(* implement the Transaction Commit specification of module $TCommit$.  In *)
(* this specification, RMs spontaneously issue $Prepared$ messages.  We    *)
(* ignore the $Prepare$ messages that the TM can send to the               *)
(* RMs.\vspace{.4em}                                                       *)
(*                                                                         *)
(* For simplicity, we also eliminate $Abort$ messages sent by an RM when   *)
(* it decides to abort.  Such a message would cause the TM to abort the    *)
(* transaction, an event represented here by the TM spontaneously deciding *)
(* to abort.\vspace{.4em}                                                  *)
(*                                                                         *)
(* This specification describes only the safety properties of the          *)
(* protocol--that is, what is allowed to happen.  What must happen would   *)
(* be described by liveness properties, which we do not specify.           *)
(***************************************************************************)
CONSTANT RM

VARIABLES
  rmState,       \* $rmState[rm]$ is the state of resource manager RM.
  tmState,       \* The state of the transaction manager.
  tmPrepared,    \* The set of RMs from which the TM has received "Prepared" messages
  msgs

vars == <<rmState, tmState, tmPrepared, msgs>>

Message ==
  (*************************************************************************)
  (* The set of all possible messages.  Messages of type $"Prepared"$ are  *)
  (* sent from the RM indicated by the message's $rm$ field to the TM\@.   *)
  (* Messages of type $"Commit"$ and $"Abort"$ are broadcast by the TM, to *)
  (* be received by all RMs.  The set $msgs$ contains just a single copy   *)
  (* of such a message.                                                    *)
  (*************************************************************************)
  [type : {"Prepared"}, rm : RM]  \cup  [type : {"Commit", "Abort"}]

Init ==   
  (*************************************************************************)
  (* The initial predicate.                                                *)
  (*************************************************************************)
  /\ rmState = [rm \in RM |-> "working"]
  /\ tmState = "init"
  /\ tmPrepared   = {}
  /\ msgs = {}
-----------------------------------------------------------------------------
(***************************************************************************)
(* We now define the actions that may be performed by the processes, first *)
(* the TM's actions, then the RMs' actions.                                *)
(***************************************************************************)
TMRcvPrepared(rm) ==
  (*************************************************************************)
  (* The TM receives a $"Prepared"$ message from resource manager $rm$.    *)
  (*************************************************************************)
  /\ tmState = "init"
  /\ [type |-> "Prepared", rm |-> rm] \in msgs
  /\ tmPrepared' = tmPrepared \cup {rm}
  /\ UNCHANGED <<rmState, tmState, msgs>>

TMCommit ==
  (*************************************************************************)
  (* The TM commits the transaction; enabled iff the TM is in its initial  *)
  (* state and every RM has sent a $"Prepared"$ message.                   *)
  (*************************************************************************)
  /\ tmState = "init"
  /\ tmPrepared = RM
  /\ tmState' = "committed"
  /\ msgs' = msgs \cup {[type |-> "Commit"]}
  /\ UNCHANGED <<rmState, tmPrepared>>

TMAbort ==
  (*************************************************************************)
  (* The TM spontaneously aborts the transaction.                          *)
  (*************************************************************************)
  /\ tmState = "init"
  /\ tmState' = "aborted"
  /\ msgs' = msgs \cup {[type |-> "Abort"]}
  /\ UNCHANGED <<rmState, tmPrepared>>

RMPrepare(rm) == 
  (*************************************************************************)
  (* Resource manager $rm$ prepares.                                       *)
  (*************************************************************************)
  /\ rmState[rm] = "working"
  /\ rmState' = [rmState EXCEPT ![rm] = "prepared"]
  /\ msgs' = msgs \cup {[type |-> "Prepared", rm |-> rm]}
  /\ UNCHANGED <<tmState, tmPrepared>>
  
RMChooseToAbort(rm) ==
  (*************************************************************************)
  (* Resource manager $rm$ spontaneously decides to abort.  As noted       *)
  (* above, $rm$ does not send any message in our simplified spec.         *)
  (*************************************************************************)
  /\ rmState[rm] = "working"
  /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>

RMRcvCommitMsg(rm) ==
  (*************************************************************************)
  (* Resource manager $rm$ is told by the TM to commit.                    *)
  (*************************************************************************)
  /\ [type |-> "Commit"] \in msgs
  /\ rmState[rm] # "committed" \* no need to commit twice.
  /\ rmState' = [rmState EXCEPT ![rm] = "committed"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>

RMRcvAbortMsg(rm) ==
  (*************************************************************************)
  (* Resource manager $rm$ is told by the TM to abort.                     *)
  (*************************************************************************)
  /\ [type |-> "Abort"] \in msgs
  /\ rmState[rm] # "aborted" \* no need to abort twice.
  /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>

Next ==
  \/ TMCommit 
  \/ TMAbort
  \/ \E rm \in RM : TMRcvPrepared(rm) 
  \/ \E rm \in RM : RMPrepare(rm) 
  \/ \E rm \in RM : RMChooseToAbort(rm)
  \/ \E rm \in RM : RMRcvCommitMsg(rm) 
  \/ \E rm \in RM : RMRcvAbortMsg(rm)
-----------------------------------------------------------------------------
\* TPSpec == Init /\ [][Next]_<<rmState, tmState, tmPrepared, msgs>>

NextUnchanged == UNCHANGED vars

TCConsistent ==  
  (*************************************************************************)
  (* A state predicate asserting that two RMs have not arrived at          *)
  (* conflicting decisions.                                                *)
  (*************************************************************************)
  \A rm1, rm2 \in RM : ~ (rmState[rm1] = "aborted" /\ rmState[rm2] = "committed")

  (*************************************************************************)
  (* The complete spec of the Two-Phase Commit protocol.                   *)
  (*************************************************************************)

------------------------------------------------------------

\* 
\* Animation definitions.
\* 

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

\* Group element. 'children' is as a sequence of elements that will be contained in this group.
Group(children, attrs) == SVGElem("g", attrs, children, "")

Injective(f) == \A x, y \in DOMAIN f : f[x] = f[y] => x = y

---------------------------------------------------------------------

CommitColor == "green"
AbortColor == "red"

\* Establish a fixed mapping to assign an ordering to elements in these sets.
\* ServerId == CHOOSE f \in [Server -> 1..Cardinality(Person)] : Injective(f)
RMId == CHOOSE f \in [1..Cardinality(RM) -> RM] : Injective(f)

\* Animation view definition.
c1 == Circle(10, 10, 3, [fill |-> "red"])
c2 == Circle(20, 10, 3, [fill |-> "red"])
\* ServerIdDomain == 1..Cardinality(Server)
RMIdDomain == 1..Cardinality(RM)

\* RM elements node circles with corresponding colors.
RMSpacing == 40
RMElems == [i \in RMIdDomain |-> Circle(RMSpacing * i, 45, 10, 
        [stroke |-> "black", fill |-> 
            IF rmState[RMId[i]] = "prepared" 
                THEN "steelblue" 
            ELSE IF rmState[RMId[i]] = "committed" THEN CommitColor 
            ELSE IF rmState[RMId[i]] = "aborted" THEN AbortColor ELSE "gray"])]

TMXpos == RMSpacing * (Cardinality(RM) + 1) \div 2
TMElem == Circle(TMXpos, 95, 10, [stroke |-> "black", fill |-> IF tmState = "committed" THEN CommitColor ELSE IF tmState = "init" THEN "gray" ELSE AbortColor])
RMTextElems == 
    [i \in RMIdDomain |->
        Text(40 * i, 30, RMId[i], ("fill" :> "black" @@ "text-anchor" :> "middle" @@ "font-size" :> "12"))
    ]
    \* <<Text(10, 10, "RM1", [fill |-> "black"]), Text(20, 10, "RM2", [fill |-> "black"]), Text(40, 50, "TM", [fill |-> "black"])>>
 
TMTextElems == <<
    Text(TMXpos, 80, "TM", ("fill" :> "black" @@ "text-anchor" :> "middle" @@ "font-size" :> "12")),
    Text(TMXpos, 120, ToString(tmPrepared), ("fill" :> "black" @@ "text-anchor" :> "middle" @@ "font-size" :> "10"))
>>
TextElems == RMTextElems \o TMTextElems


AnimView == Group(RMElems \o <<TMElem>> \o TextElems, [i \in {} |-> {}])

=============================================================================
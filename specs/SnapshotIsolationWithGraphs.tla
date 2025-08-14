------------------------- MODULE SnapshotIsolationWithGraphs -------------------------
EXTENDS Naturals, FiniteSets, Sequences, TLC

(**************************************************************************************************)
(*                                                                                                *)
(* This is a specification of snapshot isolation.  It is based on various sources, integrating    *)
(* ideas and definitions from:                                                                    *)
(*                                                                                                *)
(*     ``Making Snapshot Isolation Serializable", Fekete et al., 2005                             *)
(*     https://www.cse.iitb.ac.in/infolab/Data/Courses/CS632/2009/Papers/p492-fekete.pdf          *)
(*                                                                                                *)
(*     ``Serializable Isolation for Snapshot Databases", Cahill, 2009                             *)
(*     https://ses.library.usyd.edu.au/bitstream/2123/5353/1/michael-cahill-2009-thesis.pdf       *)
(*                                                                                                *)
(*     ``A Read-Only Transaction Anomaly Under Snapshot Isolation", Fekete et al.                 *)
(*     https://www.cs.umb.edu/~poneil/ROAnom.pdf                                                  *)
(*                                                                                                *)
(*     ``Debugging Designs", Chris Newcombe, 2011                                                 *)
(*     https://github.com/pron/amazon-snapshot-spec/blob/master/DebuggingDesigns.pdf              *)
(*                                                                                                *)
(* This spec tries to model things at a very high level of abstraction, so as to communicate the  *)
(* important concepts of snapshot isolation, as opposed to how a system might actually implement  *)
(* it.  Correctness properties and their detailed explanations are included at the end of this    *)
(* spec.  We draw the basic definition of snapshot isolation from Definition 1.1 of Fekete's      *)
(* "Read-Only" anomaly paper:                                                                     *)
(*                                                                                                *)
(*                                                                                                *)
(*     "...we assume time is measured by a counter that advances whenever any                     *)
(* transaction starts or commits, and we designate the time when transaction Ti starts as         *)
(* start(Ti) and the time when Ti commits as commit(Ti).                                          *)
(*                                                                                                *)
(* Definition 1.1: Snapshot Isolation (SI).  A transaction Ti executing under SI conceptually     *)
(* reads data from the committed state of the database as of time start(Ti) (the snapshot), and   *)
(* holds the results of its own writes in local memory store, so if it reads data it has written  *)
(* it will read its own output.  Predicates evaluated by Ti are also based on rows and index      *)
(* entry versions from the committed state of the database at time start(Ti), adjusted to take    *)
(* Ti's own writes into account.  Snapshot Isolation also must obey a "First Committer (Updater)  *)
(* Wins" rule...The interval in time from the start to the commit of a transaction, represented   *)
(* [Start(Ti), Commit(Ti)], is called its transactional lifetime.  We say two transactions T1 and *)
(* T2 are concurrent if their transactional lifetimes overlap, i.e., [start(T1), commit(T1)] ∩    *)
(* [start(T2), commit(T2)] ≠ Φ.  Writes by transactions active after Ti starts, i.e., writes by   *)
(* concurrent transactions, are not visible to Ti.  When Ti is ready to commit, it obeys the      *)
(* First Committer Wins rule, as follows: Ti will successfully commit if and only if no           *)
(* concurrent transaction Tk has already committed writes (updates) of rows or index entries that *)
(* Ti intends to write."                                                                          *)
(*                                                                                                *)
(**************************************************************************************************)


(**************************************************************************************************)
(* The constant parameters of the spec.                                                           *)
(**************************************************************************************************)

\* Set of all transaction ids.
CONSTANT txnIds

\* Set of all data store keys/values.
CONSTANT keys, values

\* An empty value.
CONSTANT Empty

(**************************************************************************************************)
(* The variables of the spec.                                                                     *)
(**************************************************************************************************)

\* The clock, which measures 'time', is just a counter, that increments (ticks) 
\* whenever a transaction starts or commits.
VARIABLE clock

\* The set of all currently running transactions.
VARIABLE runningTxns

\* The full history of all transaction operations. It is modeled as a linear 
\* sequence of events. Such a history would likely never exist in a real implementation, 
\* but it is used in the model to check the properties of snapshot isolation.
VARIABLE txnHistory

\* (NOT NECESSARY)
\* The key-value data store. In this spec, we model a data store explicitly, even though it is not actually
\* used for the verification of any correctness properties. This was added initially as an attempt the make the
\* spec more intuitive and understandable. It may play no important role at this point, however. If a property
\* check was ever added for view serializability, this, and the set of transaction snapshots, may end up being
\* useful.
VARIABLE dataStore

\* (NOT NECESSARY)
\* The set of snapshots needed for all running transactions. Each snapshot 
\* represents the entire state of the data store as of a given point in time. 
\* It is a function from transaction ids to data store snapshots. This, like the 'dataStore' variable, may 
\* now be obsolete for a spec at this level of abstraction, since the correctness properties we check do not 
\* depend on the actual data being read/written.
VARIABLE txnSnapshots

\* All the variables that are used in the new RW edge detection definition of Snapshot Isolation are defined below.

\* The set of all incoming edges to a given transaction. Used to detect dangerous edge sequences in the algorithm.
VARIABLE incomingEdges

\* The set of all outgoing edges from a given transaction. Used to detect dangerous edge sequences in the algorithm.
VARIABLE outgoingEdges

\* The set of transactions that are concurrent with a given transaction.
VARIABLE concurrentTxns


vars == <<clock, runningTxns, txnSnapshots, dataStore, txnHistory, incomingEdges, outgoingEdges, concurrentTxns>>


(**************************************************************************************************)
(* Data type definitions.                                                                         *)
(**************************************************************************************************)

DataStoreType == [keys -> (values \cup {Empty})]
BeginOpType   == [type : {"begin"}  , txnId : txnIds , time : Nat]
CommitOpType  == [type : {"commit"} , txnId : txnIds , time : Nat, updatedKeys : SUBSET keys]
WriteOpType   == [type : {"write"}  , txnId : txnIds , key: SUBSET keys , val : SUBSET values]
ReadOpType    == [type : {"read"}   , txnId : txnIds , key: SUBSET keys , val : SUBSET values]
AnyOpType     == UNION {BeginOpType, CommitOpType, WriteOpType, ReadOpType}

(**************************************************************************************************)
(* The type invariant and initial predicate.                                                      *)
(**************************************************************************************************)

TypeInvariant == 
    \* /\ txnHistory \in Seq(AnyOpType) seems expensive to check with TLC, so disable it.
    /\ dataStore    \in DataStoreType
    /\ txnSnapshots \in [txnIds -> (DataStoreType \cup {Empty})]
    /\ runningTxns  \in SUBSET [ id : txnIds, 
                                 startTime  : Nat, 
                                 commitTime : Nat \cup {Empty}]
    /\ incomingEdges \in [txnIds -> SUBSET (txnIds \X {"WW", "WR", "RW"})] \* Map from transaction id to set of (incoming transaction, edge type) pairs.
    /\ outgoingEdges \in [txnIds -> SUBSET (txnIds \X {"WW", "WR", "RW"})] \* Map from transaction id to set of (outgoing transaction, edge type) pairs.
    /\ concurrentTxns \in [txnIds -> SUBSET txnIds] \* Map from transaction id to set of concurrent transaction ids. Set at begin time.

Init ==  
    /\ runningTxns = {} 
    /\ txnHistory = <<>>
    /\ clock = 0
    /\ txnSnapshots = [id \in txnIds |-> Empty]
    /\ dataStore = [k \in keys |-> Empty]
    /\ incomingEdges = [id \in txnIds |-> {}] \* Initially no incoming edges.
    /\ outgoingEdges = [id \in txnIds |-> {}] \* Initially no outgoing edges.
    /\ concurrentTxns = [id \in txnIds |-> {}] \* Initially no concurrent transactions.

(**************************************************************************************************)
(* Helpers for querying transaction histories.                                                    *)
(*                                                                                                *)
(* These are parameterized on a transaction history and a transaction id, if applicable.          *)
(**************************************************************************************************)

\* Generic TLA+ helper.
Range(f) == {f[x] : x \in DOMAIN f}

\* The begin or commit op for a given transaction id.
BeginOp(h, txnId)  == CHOOSE op \in Range(h) : op.txnId = txnId /\ op.type = "begin"
CommitOp(h, txnId) == CHOOSE op \in Range(h) : op.txnId = txnId /\ op.type = "commit"

\* The set of all committed/aborted transaction ids in a given history.
CommittedTxns(h) == {op.txnId : op \in {op \in Range(h) : op.type = "commit"}}
AbortedTxns(h)   == {op.txnId : op \in {op \in Range(h) : op.type = "abort"}}

\* The set of all read or write ops done by a given transaction.                   
ReadsByTxn(h, txnId)  == {op \in Range(h) : op.txnId = txnId /\ op.type = "read"}
WritesByTxn(h, txnId) == {op \in Range(h) : op.txnId = txnId /\ op.type = "write"}

\* The set of all keys read or written to by a given transaction.                   
KeysReadByTxn(h, txnId)    == { op.key : op \in ReadsByTxn(txnHistory, txnId)}
KeysWrittenByTxn(h, txnId) == { op.key : op \in WritesByTxn(txnHistory, txnId)}

\* The index of a given operation in the transaction history sequence.
IndexOfOp(h, op) == CHOOSE i \in DOMAIN h : h[i] = op

RunningTxnIds == {txn.id : txn \in runningTxns}

\* Checks if two transactions are concurrent (their lifetimes overlap).
\* Two transactions are concurrent if they were running at the same time.
\* Uses commit time if available, otherwise considers the transaction as still running.
AreConcurrent(h, t1Id, t2Id) ==
    /\ t1Id /= t2Id
    /\ \E t1BeginOp \in Range(h) : t1BeginOp.txnId = t1Id /\ t1BeginOp.type = "begin"
    /\ \E t2BeginOp \in Range(h) : t2BeginOp.txnId = t2Id /\ t2BeginOp.type = "begin"
    /\ LET t1Start == BeginOp(h, t1Id).time
           t2Start == BeginOp(h, t2Id).time
           \* Get commit time if transaction committed, otherwise use a very large number
           t1End == IF t1Id \in CommittedTxns(h) THEN CommitOp(h, t1Id).time ELSE 999999
           t2End == IF t2Id \in CommittedTxns(h) THEN CommitOp(h, t2Id).time ELSE 999999
       IN
       \* Check if intervals [t1Start, t1End] and [t2Start, t2End] overlap
       /\ t1Start <= t2End
       /\ t2Start <= t1End

(**************************************************************************************************)
(*                                                                                                *)
(* Action Definitions                                                                             *)
(*                                                                                                *)
(**************************************************************************************************)


(**************************************************************************************************)
(* When a transaction starts, it gets a new, unique transaction id and is added to the set of     *)
(* running transactions.  It also "copies" a local snapshot of the data store on which it will    *)
(* perform its reads and writes against.  In a real system, this data would not be literally      *)
(* "copied", but this is the fundamental concept of snapshot isolation i.e.  that each            *)
(* transaction appears to operate on its own local snapshot of the database.                      *)
(**************************************************************************************************)
StartTxn(newTxnId) == 
    LET newTxn == 
        [ id |-> newTxnId, 
            startTime |-> clock+1, 
            commitTime |-> Empty] IN
    \* Must choose an unused transaction id. There must be no other operation
    \* in the history that already uses this id.
    /\ ~\E op \in Range(txnHistory) : op.txnId = newTxnId
    \* Save a snapshot of current data store for this transaction, and
    \* and append its 'begin' event to the history.
    /\ txnSnapshots' = [txnSnapshots EXCEPT ![newTxnId] = dataStore]
    /\ LET beginOp == [ type  |-> "begin", 
                        txnId |-> newTxnId, 
                        time  |-> clock+1 ] IN
        txnHistory' = Append(txnHistory, beginOp)
    \* Add transaction to the set of active transactions.
    /\ runningTxns' = runningTxns \cup {newTxn}
    \* Tick the clock.
    /\ clock' = clock + 1
    \* Add to this transaction's set of concurrent transactions, all the running transactions.
    /\ concurrentTxns' = [concurrentTxns EXCEPT ![newTxnId] = RunningTxnIds]
    /\ UNCHANGED <<dataStore, incomingEdges, outgoingEdges>>
                                                  
(**************************************************************************************************)
(* When a transaction T0 is ready to commit, it obeys the "First Committer Wins" rule.  T0 will   *)
(* only successfully commit if no concurrent transaction has already committed writes of data     *)
(* objects that T0 intends to write.  Transactions T0, T1 are considered concurrent if the        *)
(* intersection of their timespans is non empty i.e.                                              *)
(*                                                                                                *)
(*     [start(T0), commit(T0)] \cap [start(T1), commit(T1)] != {}                                 *)
(**************************************************************************************************)

\* Checks whether a given transaction is allowed to commit based on RW edge cycle prevention
TxnCanCommit(txnId) ==
    \* Check if committing this transaction would create a dangerous cycle
    \* Case 1: If txnId has an incoming RW edge from T1 to txnId
    \* Check if T1 has any incoming RW edges OR if txnId has any outgoing RW edges
    \* If BOTH are false (neither has the additional edges), then txnId must abort
    /\ ~(\E <<t1, edgeType>> \in incomingEdges[txnId] :
        /\ edgeType = "RW"
        /\ ~(\E <<src, et>> \in incomingEdges[t1] : et = "RW")  \* T1 has no incoming RW edges
        /\ ~(\E <<dst, et>> \in outgoingEdges[txnId] : et = "RW"))  \* txnId has no outgoing RW edges
    \* Case 2: If txnId has an outgoing RW edge from txnId to T2
    \* Check if txnId has any incoming RW edges OR if T2 has any outgoing RW edges
    \* If BOTH are false (neither has the additional edges), then txnId must abort
    /\ ~(\E <<t2, edgeType>> \in outgoingEdges[txnId] :
        /\ edgeType = "RW"
        /\ ~(\E <<src, et>> \in incomingEdges[txnId] : et = "RW")  \* txnId has no incoming RW edges
        /\ ~(\E <<dst, et>> \in outgoingEdges[t2] : et = "RW"))  \* T2 has no outgoing RW edges
         
CommitTxn(txnId) == 
    \* Transaction must be able to commit i.e. have no write conflicts with concurrent.
    \* committed transactions.
    /\ txnId \in RunningTxnIds
    \* Must not be a no-op transaction.
    /\ (WritesByTxn(txnHistory, txnId) \cup ReadsByTxn(txnHistory, txnId)) /= {}  
    \* RW EDGE DETECTION
    \* Update concurrent transactions to include:
    \* 1. Current concurrent transactions set
    \* 2. Currently running transactions (except self)
    \* 3. Committed transactions that started after this transaction started
    \* 4. Aborted transactions dont matter since they are essentially invisible to the current transaction.
    /\ LET myStartTime == BeginOp(txnHistory, txnId).time
           committedAfterMyStart == {tid \in CommittedTxns(txnHistory) : 
                                      BeginOp(txnHistory, tid).time > myStartTime}
           updatedConcurrentSet == concurrentTxns[txnId] 
                                  \cup (RunningTxnIds \ {txnId}) 
                                  \cup committedAfterMyStart
           keysReadByMe == KeysReadByTxn(txnHistory, txnId)
           \* Find concurrent transactions that wrote to keys that txnId read
           rwTargets == {otherTxn \in updatedConcurrentSet : 
                           KeysWrittenByTxn(txnHistory, otherTxn) \cap keysReadByMe /= {}}
           \* Create new RW edges
           newOutgoingRW == {<<target, "RW">> : target \in rwTargets}
           \* Update outgoing edges for this transaction
           updatedOutgoing == [outgoingEdges EXCEPT ![txnId] = outgoingEdges[txnId] \cup newOutgoingRW]
           \* Update incoming edges for the target transactions
           updatedIncoming == [tid \in txnIds |->
                                IF tid \in rwTargets
                                THEN incomingEdges[tid] \cup {<<txnId, "RW">>}
                                ELSE incomingEdges[tid]]
           \* Update the global concurrent transactions mapping
           updatedConcurrentTxns == [concurrentTxns EXCEPT ![txnId] = updatedConcurrentSet]
           
           \* WW EDGE DETECTION
           \* Find concurrent transactions that wrote to keys that txnId also wrote to
           keysWrittenByMe == KeysWrittenByTxn(txnHistory, txnId)
           wwTargets == {otherTxn \in updatedConcurrentSet : 
                           KeysWrittenByTxn(txnHistory, otherTxn) \cap keysWrittenByMe /= {}}
           \* Create new WW edges
           newOutgoingWW == {<<target, "WW">> : target \in wwTargets}
           \* Update outgoing edges for this transaction (combining RW and WW edges)
           finalOutgoing == [outgoingEdges EXCEPT ![txnId] = outgoingEdges[txnId] \cup newOutgoingRW \cup newOutgoingWW]
           \* Update incoming edges for the target transactions (combining RW and WW targets)
           finalIncoming == [tid \in txnIds |->
                                IF tid \in rwTargets
                                THEN (IF tid \in wwTargets 
                                      THEN incomingEdges[tid] \cup {<<txnId, "RW">>, <<txnId, "WW">>}
                                      ELSE incomingEdges[tid] \cup {<<txnId, "RW">>})
                                ELSE (IF tid \in wwTargets
                                      THEN incomingEdges[tid] \cup {<<txnId, "WW">>}
                                      ELSE incomingEdges[tid])]
       IN
       /\ outgoingEdges' = finalOutgoing
       /\ incomingEdges' = finalIncoming
       /\ concurrentTxns' = updatedConcurrentTxns

    \* Check if the transaction can commit.
    \* All data structures need to be updated incase the transaction aborts so that the information is preserved.

    \* /\ TxnCanCommit(txnId)
    
    \* We can leave the snapshot around, since it won't be used again.
    /\ LET commitOp == [ type          |-> "commit", 
                         txnId         |-> txnId, 
                         time          |-> clock + 1,
                         updatedKeys   |-> KeysWrittenByTxn(txnHistory, txnId)] IN
       txnHistory' = Append(txnHistory, commitOp)            
    \* Merge this transaction's updates into the data store. If the 
    \* transaction has updated a key, then we use its version as the new
    \* value for that key. Otherwise the key remains unchanged.
    /\ dataStore' = [k \in keys |-> IF k \in KeysWrittenByTxn(txnHistory, txnId) 
                                        THEN txnSnapshots[txnId][k]
                                        ELSE dataStore[k]]
    \* Remove the transaction from the active set. 
    /\ runningTxns' = {r \in runningTxns : r.id # txnId}
    /\ clock' = clock + 1

    /\ UNCHANGED <<txnSnapshots>>

(**************************************************************************************************)
(* In this spec, a transaction aborts if and only if it cannot commit, due to write conflicts.    *)
(**************************************************************************************************)
AbortTxn(txnId) ==
    \* If a transaction can't commit due to write conflicts, then it
    \* must abort.
    /\ FALSE
    /\ txnId \in RunningTxnIds
    \* Must not be a no-op transaction.
    /\ (WritesByTxn(txnHistory, txnId) \cup ReadsByTxn(txnHistory, txnId)) /= {}
    /\ ~TxnCanCommit(txnId)
    /\ LET abortOp == [ type   |-> "abort", 
                        txnId  |-> txnId, 
                        time   |-> clock + 1] IN    
       txnHistory' = Append(txnHistory, abortOp)
    /\ runningTxns' = {r \in runningTxns : r.id # txnId} \* transaction is no longer running.
    /\ clock' = clock + 1
    \* No changes are made to the data store.
    /\ UNCHANGED <<dataStore, txnSnapshots, incomingEdges, outgoingEdges, concurrentTxns>>

(***************************************************************************************************)
(* Read and write operations executed by transactions.                                            *)
(*                                                                                                *)
(* As a simplification, and to limit the size of potential models, we allow transactions to only  *)
(* read or write to the same key once.  The idea is that it limits the state space without loss   *)
(* of generality.                                                                                 *)
(**************************************************************************************************)

TxnRead(txnId, k) == 
    \* Read from this transaction's snapshot.
    \* Update the transaction's incoming and outgoing edges based on RW edge detection.
    /\ txnId \in RunningTxnIds
    /\ LET valRead == txnSnapshots[txnId][k]
           readOp == [ type  |-> "read", 
                       txnId |-> txnId, 
                       key   |-> k, 
                       val   |-> valRead]
           \* WR EDGE DETECTION
           \* Update the transactions's concurrent transactions set.
           myStartTime == BeginOp(txnHistory, txnId).time
           committedAfterMyStart == {tid \in CommittedTxns(txnHistory) : 
                                     BeginOp(txnHistory, tid).time > myStartTime}
           updatedConcurrentSet == concurrentTxns[txnId] 
                                  \cup (RunningTxnIds \ {txnId}) 
                                  \cup committedAfterMyStart
           keysReadByMe == KeysReadByTxn(txnHistory, txnId)
           \* Find transactions that wrote to the keys that this transaction read. From the set of transactions that committed before this transaction started.
           exclusiveCommitSet == {tid \in CommittedTxns(txnHistory) :
                                  CommitOp(txnHistory, tid).time < myStartTime}
           rwTargets == {otherTxn \in exclusiveCommitSet : 
                         KeysWrittenByTxn(txnHistory, otherTxn) \cap keysReadByMe /= {}}
           \* Create new WR edges
           newOutgoingWR == {<<target, "WR">> : target \in rwTargets}
           \* Update outgoing edges for this transaction
           updatedOutgoing == [outgoingEdges EXCEPT ![txnId] = outgoingEdges[txnId] \cup newOutgoingWR]
           \* Update incoming edges for the target transactions
           updatedIncoming == [tid \in txnIds |->
                               IF tid \in rwTargets
                               THEN incomingEdges[tid] \cup {<<txnId, "WR">>}
                               ELSE incomingEdges[tid]]
           \* Update the global concurrent transactions mapping
           updatedConcurrentTxns == [concurrentTxns EXCEPT ![txnId] = updatedConcurrentSet]
       IN
       /\ k \notin KeysReadByTxn(txnHistory, txnId)   
       /\ txnHistory' = Append(txnHistory, readOp)
       /\ outgoingEdges' = updatedOutgoing
       /\ incomingEdges' = updatedIncoming
       /\ concurrentTxns' = updatedConcurrentTxns
       /\ UNCHANGED <<dataStore, clock, runningTxns, txnSnapshots>>
                   
TxnUpdate(txnId, k, v) == 
    /\ txnId \in RunningTxnIds
    /\ LET writeOp == [ type  |-> "write", 
                        txnId |-> txnId, 
                        key   |-> k, 
                        val   |-> v] IN  
        /\ k \notin KeysWrittenByTxn(txnHistory, txnId)
        \* We update the transaction's snapshot, not the actual data store.
        /\ LET updatedSnapshot == [txnSnapshots[txnId] EXCEPT ![k] = v] IN
            txnSnapshots' = [txnSnapshots EXCEPT ![txnId] = updatedSnapshot]
        /\ txnHistory' = Append(txnHistory, writeOp)
        /\ UNCHANGED <<dataStore, runningTxns, clock, concurrentTxns, incomingEdges, outgoingEdges>>

(**************************************************************************************************)
(* The next-state relation and spec definition.                                                   *)
(*                                                                                                *)
(* Since it is desirable to have TLC check for deadlock, which may indicate bugs in the spec or   *)
(* in the algorithm, we want to explicitly define what a "valid" termination state is.  If all    *)
(* transactions have run and either committed or aborted, we consider that valid termination, and *)
(* is allowed as an infinite suttering step.                                                      *)
(*                                                                                                *)
(* Also, once a transaction knows that it cannot commit due to write conflicts, we don't let it   *)
(* do any more reads or writes, so as to eliminate wasted operations.  That is, once we know a    *)
(* transaction can't commit, we force its next action to be abort.                                *)
(**************************************************************************************************)           

AllTxnsFinished == AbortedTxns(txnHistory) \cup CommittedTxns(txnHistory) = txnIds
    
Next == 
    \/ \E tid \in txnIds : StartTxn(tid)
    \* Ends a given transaction by either committing or aborting it. To exclude uninteresting 
    \* histories, we require that a transaction does at least one operation before committing or aborting. 
    \* Assumes that the given transaction is currently running.
    \/ \E tid \in txnIds : CommitTxn(tid)
    \* \/ \E tid \in txnIds : AbortTxn(tid)
    \* Transaction reads or writes a key. We limit transactions
    \* to only read or write the same key once.
    \/ \E tid \in txnIds, k \in keys : TxnRead(tid, k)
    \/ \E tid \in txnIds, k \in keys, v \in values : TxnUpdate(tid, k, v)
    \/ (AllTxnsFinished /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)


----------------------------------------------------------------------------------------------------


(**************************************************************************************************)
(*                                                                                                *)
(* Correctness Properties and Tests                                                               *)
(*                                                                                                *)
(**************************************************************************************************)



(**************************************************************************************************)
(* Operator for computing cycles in a given graph, defined by a set of edges.                     *)
(*                                                                                                *)
(* Returns a set containing all elements that participate in any cycle (i.e.  union of all        *)
(* cycles), or an empty set if no cycle is found.                                                 *)
(*                                                                                                *)
(* Source:                                                                                        *)
(* https://github.com/pron/amazon-snapshot-spec/blob/master/serializableSnapshotIsolation.tla.    *)
(**************************************************************************************************)
FindAllNodesInAnyCycle(edges) ==

    LET RECURSIVE findCycleNodes(_, _)   (* startNode, visitedSet *)
        (* Returns a set containing all elements of some cycle starting at startNode,
           or an empty set if no cycle is found. 
         *)
        findCycleNodes(node, visitedSet) ==
            IF node \in visitedSet THEN
                {node}  (* found a cycle, which includes node *)
            ELSE
                LET newVisited == visitedSet \union {node}
                    neighbors == {to : <<from, to>> \in 
                                           {<<from, to>> \in edges : from = node}}
                IN  (* Explore neighbors *)
                    UNION {findCycleNodes(neighbor, newVisited) : neighbor \in neighbors}
                    
        startPoints == {from : <<from, to>> \in edges}  (* All nodes with an outgoing edge *)
    IN 
        UNION {findCycleNodes(node, {}) : node \in startPoints}
       
IsCycle(edges) == FindAllNodesInAnyCycle(edges) /= {}



(**************************************************************************************************)
(*                                                                                                *)
(* Verifying Serializability                                                                      *)
(*                                                                                                *)
(* ---------------------------------------                                                        *)
(*                                                                                                *)
(* For checking serializability of transaction histories we use the "Conflict Serializability"    *)
(* definition.  This is slightly different than what is known as "View Serializability", but is   *)
(* suitable for verification, since it is efficient to check, whereas checking view               *)
(* serializability of a transaction schedule is known to be NP-complete.                          *)
(*                                                                                                *)
(* The definition of conflict serializability permits a more limited set of transaction           *)
(* histories.  Intuitively, it can be viewed as checking whether a given schedule has the         *)
(* "potential" to produce a certain anomaly, even if the particular data values for a history     *)
(* make it serializable.  Formally, we can think of the set of conflict serializable histories as *)
(* a subset of all possible serializable histories.  Alternatively, we can say that, for a given  *)
(* history H ConflictSerializable(H) => ViewSerializable(H).  The converse, however, is not true. *)
(* A history may be view serializable but not conflict serializable.                              *)
(*                                                                                                *)
(* In order to check for conflict serializability, we construct a multi-version serialization     *)
(* graph (MVSG).  Details on MVSG can be found, among other places, in Cahill's thesis, Section   *)
(* 2.5.1.  To construct the MVSG, we put an edge from one committed transaction T1 to another     *)
(* committed transaction T2 in the following situations:                                          *)
(*                                                                                                *)
(*   (WW-Dependency)                                                                              *)
(*   T1 produces a version of x, and T2 produces a later version of x.                            *)
(*                                                                                                *)
(*   (WR-Dependency)                                                                              *)
(*   T1 produces a version of x, and T2 reads this (or a later) version of x.                     *)
(*                                                                                                *)
(*   (RW-Dependency)                                                                              *)
(*   T1 reads a version of x, and T2 produces a later version of x. This is                       *)
(*   the only case where T1 and T2 can run concurrently.                                          *)
(*                                                                                                *)
(**************************************************************************************************)

\* T1 wrote to a key that T2 then also wrote to. The First Committer Wins rule implies
\* that T1 must have committed before T2 began.
WWDependency(h, t1Id, t2Id) == 
    \E op1 \in WritesByTxn(h, t1Id) :
    \E op2 \in WritesByTxn(h, t2Id) :
        /\ op1.key = op2.key
        /\ CommitOp(h, t1Id).time < CommitOp(h, t2Id).time

\* T1 wrote to a key that T2 then later read, after T1 committed.
WRDependency(h, t1Id, t2Id) == 
    \E op1 \in WritesByTxn(h, t1Id) :
    \E op2 \in ReadsByTxn(h, t2Id) :
        /\ op1.key = op2.key
        /\ CommitOp(h, t1Id).time < BeginOp(h, t2Id).time   

\* T1 read a key that T2 then later wrote to. T1 must start before T2 commits, since this implies that T1 read  
\* a version of the key and T2 produced a later version of that ke, i.e. when it commits. T1, however, read 
\* an earlier version of that key, because it started before T2 committed.
RWDependency(h, t1Id, t2Id) == 
    \E op1 \in ReadsByTxn(h, t1Id) :
    \E op2 \in WritesByTxn(h, t2Id) :
        /\ op1.key = op2.key
        /\ BeginOp(h, t1Id).time < CommitOp(h, t2Id).time  \* T1 starts before T2 commits. This means that T1 read
        

\* Produces the serialization graph as defined above, for a given history. This graph is produced 
\* by defining the appropriate set comprehension, where the produced set contains all the edges of the graph.
SerializationGraph(history) == 
    LET committedTxnIds == CommittedTxns(history) IN
    {tedge \in (committedTxnIds \X committedTxnIds):
        /\ tedge[1] /= tedge[2]
        /\ \/ WWDependency(history, tedge[1], tedge[2])
           \/ WRDependency(history, tedge[1], tedge[2])
           \/ RWDependency(history, tedge[1], tedge[2])}

\* The key property to verify i.e. serializability of transaction histories.
IsConflictSerializable(h) == ~IsCycle(SerializationGraph(h))

\* Examples of each dependency type.
HistWW == << [type |-> "begin"  , txnId |-> 0 , time |-> 0],
             [type |-> "write"  , txnId |-> 0 , key  |-> "k1" , val |-> "v1"],
             [type |-> "commit" , txnId |-> 0 , time |-> 1, updatedKeys |-> {"k1"}],
             [type |-> "begin"  , txnId |-> 1 , time |-> 2],
             [type |-> "write"  , txnId |-> 1 , key  |-> "k1" , val |-> "v1"],
             [type |-> "commit" , txnId |-> 1 , time |-> 3, updatedKeys |-> {"k1"}]>>

HistWR == << [type |-> "begin"  , txnId |-> 0 , time |-> 0],
             [type |-> "write"  , txnId |-> 0 , key  |-> "k1" , val |-> "v1"],
             [type |-> "commit" , txnId |-> 0 , time |-> 1, updatedKeys |-> {"k1"}],
             [type |-> "begin"  , txnId |-> 1 , time |-> 2],
             [type |-> "read"   , txnId |-> 1 , key  |-> "k1" , val |-> "v1"],
             [type |-> "commit" , txnId |-> 1 , time |-> 3, updatedKeys |-> {}]>>

HistRW == << [type |-> "begin"  , txnId |-> 0 , time |-> 0],
             [type |-> "read"   , txnId |-> 0 , key  |-> "k1" , val |-> "empty"],
             [type |-> "begin"  , txnId |-> 1 , time |-> 1],
             [type |-> "write"   , txnId |-> 1 , key  |-> "k1" , val |-> "v1"],
             [type |-> "commit" , txnId |-> 1 , time |-> 2, updatedKeys |-> {}],
             [type |-> "commit" , txnId |-> 0 , time |-> 3, updatedKeys |-> {"k1"}]>>

\* A simple invariant to test the correctness of dependency definitions.
WWDependencyCorrect == WWDependency(HistWW, 0, 1)
WRDependencyCorrect == WRDependency(HistWR, 0, 1)
RWDependencyCorrect == RWDependency(HistRW, 0, 1)
MVSGDependencyCorrect == WWDependencyCorrect /\ WRDependencyCorrect /\ RWDependencyCorrect
   
     
(**************************************************************************************************)
(* Examples of concurrency phenomena under Snapshot Isolation.  These are for demonstration       *)
(* purposes and can be used for checking the above definitions of serializability.                *)
(*                                                                                                *)
(* Write Skew:                                                                                    *)
(*                                                                                                *)
(* Example history from Michael Cahill's Phd thesis:                                              *)
(*                                                                                                *)
(* Section 2.5.1, pg.  16                                                                         *)
(* https://ses.library.usyd.edu.au/bitstream/2123/5353/1/michael-cahill-2009-thesis.pdf           *)
(*                                                                                                *)
(* H: r1(x=50) r1(y=50) r2(x=50) r2(y=50) w1(x=-20) w2(y=-30) c1 c2                               *)
(*                                                                                                *)
(*                                                                                                *)
(* Read-Only Anomaly:                                                                             *)
(*                                                                                                *)
(* "A Read-Only Transaction Anomaly Under Snapshot Isolation", Fekete, O'Neil, O'Neil             *)
(* https://www.cs.umb.edu/~poneil/ROAnom.pdf                                                      *)
(*                                                                                                *)
(*                                                                                                *)
(**************************************************************************************************)

WriteSkewAnomalyTest == <<
    [type |-> "begin",  txnId |-> 1, time |-> 1],                       
    [type |-> "begin",  txnId |-> 2, time |-> 2],
    [type |-> "read",   txnId |-> 1, key |-> "X", val |-> "Empty"],                      
    [type |-> "read",   txnId |-> 1, key |-> "Y", val |-> "Empty"],                      
    [type |-> "read",   txnId |-> 2, key |-> "X", val |-> "Empty"],                      
    [type |-> "read",   txnId |-> 2, key |-> "Y", val |-> "Empty"],                    
    [type |-> "write",  txnId |-> 1, key |-> "X", val |-> 30],           
    [type |-> "write",  txnId |-> 2, key |-> "Y", val |-> 20],        
    [type |-> "commit", txnId |-> 1, time |-> 3, updatedKeys |-> {"X"}],
    [type |-> "commit", txnId |-> 2, time |-> 4, updatedKeys |-> {"Y"}]>>

ReadOnlyAnomalyTest == <<
    [type |-> "begin",  txnId |-> 0, time |-> 0], 
    [type |-> "write",  txnId |-> 0, key |-> "K_X", val |-> 0], 
    [type |-> "write",  txnId |-> 0, key |-> "K_Y", val |-> 0], 
    [type |-> "commit", txnId |-> 0, time |-> 1, updatedKeys |-> {"K_X", "K_Y"}],
    
    (* the history from the paper *) 
                     [type |-> "begin",  txnId |-> 2, time |-> 2], 
    (* R2(X0,0)   *) [type |-> "read",   txnId |-> 2, key |-> "K_X", ver |-> "T_0"], 
    (* R2(Y0,0)   *) [type |-> "read",   txnId |-> 2, key |-> "K_Y", ver |-> "T_0"],
                      
                     [type |-> "begin",  txnId |-> 1, time |-> 3], 
    (* R1(Y0,0)   *) [type |-> "read",   txnId |-> 1, key |-> "K_Y"], 
    (* W1(Y1,20)  *) [type |-> "write",  txnId |-> 1, key |-> "K_Y", val |-> 20],
    (* C1         *) [type |-> "commit", txnId |-> 1, time |-> 4, updatedKeys |-> {"K_Y"}],
     
                     [type |-> "begin",  txnId |-> 3, time |-> 5], 
    (* R3(X0,0)   *) [type |-> "read",   txnId |-> 3, key |-> "K_X", ver |-> "T_0"], 
    (* R3(Y1,20)  *) [type |-> "read",   txnId |-> 3, key |-> "K_Y", ver |-> "T_1"], 
    (* C3         *) [type |-> "commit", txnId |-> 3, time |-> 6, updatedKeys |-> {}],
                      
    (* W2(X2,-11) *) [type |-> "write",  txnId |-> 2, key |-> "K_X", val |-> (0 - 11)], 
    (* C2         *) [type |-> "commit", txnId |-> 2, time |-> 7, updatedKeys |-> {"K_X"}]
    >>

(**************************************************************************************************)
(* Checks if a given history contains a "read-only" anomaly.  In other words, is this a           *)
(* non-serializable transaction history such that it contains a read-only transaction T, and      *)
(* removing T from the history makes the history serializable.                                    *)
(**************************************************************************************************)

ReadOnlyAnomaly(h) == 
    /\ ~IsConflictSerializable(h)
    /\ \E txnId \in CommittedTxns(h) :
        \* Transaction only did reads.
        /\ WritesByTxn(h, txnId) = {}
        \* Removing the transaction makes the history serializable
        /\ LET txnOpsFilter(t) == (t.txnId # txnId)
           hWithoutTxn == SelectSeq(h, txnOpsFilter) IN
           IsConflictSerializable(hWithoutTxn)

\* Invariant definitions.
IsConflictSerializableInv == IsConflictSerializable(txnHistory)
NoReadOnlyAnomaly == ~ReadOnlyAnomaly(txnHistory)

(**************************************************************************************************)
(* Checks if a given history contains a "write skew" anomaly.  In other words, is this a          *)
(* non-serializable transaction history such that it contains two transactions T1, T2, where T1   *)
(* writes to a key that T2 also writes to, and T1 commits before T2 starts.                      *)
(**************************************************************************************************)

---------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

\* Creates a serialization graph from the tracked edges in incomingEdges/outgoingEdges
\* This uses the actual edges detected during transaction execution
TrackedSerializationGraph == 
    LET \* Get all transaction IDs that have participated in the history
        allTxns == {tid \in txnIds : \E op \in Range(txnHistory) : op.txnId = tid}
        \* Union of edges from both incoming and outgoing perspectives
        \* For incoming edges into T: <<src, T, edgeType>>
        incomingEdgeSet == UNION {
            {<<src, tid, edgeType, 
              IF AreConcurrent(txnHistory, src, tid) THEN "concurrent" ELSE "not_concurrent">> : 
                <<src, edgeType>> \in incomingEdges[tid]}
            : tid \in allTxns
        }
        \* For outgoing edges from T: <<T, dst, edgeType>>
        outgoingEdgeSet == UNION {
            {<<tid, dst, edgeType, 
              IF AreConcurrent(txnHistory, tid, dst) THEN "concurrent" ELSE "not_concurrent">> : 
                <<dst, edgeType>> \in outgoingEdges[tid]}
            : tid \in allTxns
        }
    IN
    \* Union both sets
    incomingEdgeSet \cup outgoingEdgeSet


(**************************************************************************************************)
(* View Serializability (Experimental).                                                           *)
(*                                                                                                *)
(* A transaction history is view serializable if the reads and writes of all transaction          *)
(* oeprations are equivalent the reads and writes of some serial schedule.  View serializability  *)
(* encodes a more intuitive notion of serializability i.e.  the overall effect of a sequence of   *)
(* interleaved transactions is the same as if it they were executed in sequential order.          *)
(**************************************************************************************************)

Maximum(S) == CHOOSE x \in S : \A y \in S : y <= x

\* The set of all permutations of elements of a set S whose length are the cardinality of S.
SeqPermutations(S) == LET D == 1..Cardinality(S) IN {f \in [D -> S] : \A w \in S : \E v \in D : f[v]=w}

\* Flattens a sequence of sequences.
RECURSIVE Flatten(_)
Flatten(seq) == IF Len(seq) = 0 THEN <<>> ELSE Head(seq) \o Flatten(Tail(seq))

\* The subsequence of all operations executed by a given transaction id in a history. The original ordering 
\* of the operations is maintained.
OpsForTxn(h, txnId) == SelectSeq(h, LAMBDA t : t.txnId = txnId)
SerialHistories(h) == 
    LET serialOrderings == SeqPermutations({ OpsForTxn(h, tid) : tid \in CommittedTxns(h) }) IN
    {Flatten(o) : o \in serialOrderings}

\* We "execute" a given serial history. To do this, we really only need to determine what the new values of the 
\* 'read' operations are, since writes are not changed. To do this, we simply replace the value of each read operation
\* in the history with the appropriate one.
ExecuteSerialHistory(h) ==
    [i \in DOMAIN h |-> 
        IF h[i].type = "read" 
            \* We need to determine what value to read for this operation; we use the
            \* the value of the last write to this key.
            THEN LET prevWriteOpInds == {ind \in DOMAIN h : 
                                                /\  ind < i 
                                                /\  h[ind].type = "write"
                                                /\  h[ind].key = h[i].key} IN
                     IF prevWriteOpInds = {} 
                        THEN [h[i] EXCEPT !.val = Empty]
                        ELSE LET latestWriteOpToKey == h[Maximum(prevWriteOpInds)] IN
                             [h[i] EXCEPT !.val = latestWriteOpToKey.val] 
            ELSE h[i]]

IsViewEquivalent(h1, h2) == 
    \A tid \in CommittedTxns(h1) : OpsForTxn(h1, tid) = OpsForTxn(h2, tid)

ViewEquivalentHistory(h) == {ExecuteSerialHistory(serial) : serial \in 
                                {h2 \in SerialHistories(h) : IsViewEquivalent(h, ExecuteSerialHistory(h2))}}

IsViewSerializable(h) == \E h2 \in SerialHistories(h) : IsViewEquivalent(h, ExecuteSerialHistory(h2))


(**************************************************************************************************)
(* Experiments for G-Single and G-Nonadjacent Anomaly Cycle detection                             *)
(**************************************************************************************************)

GSingle3NodeCycleTest == <<
    [type |-> "begin",  txnId |-> 0, time |-> 1],
    [type |-> "begin",  txnId |-> 1, time |-> 2],
    [type |-> "begin",  txnId |-> 2, time |-> 3],

    \* T2 reads k1 early (for T0→RW T2)
    [type |-> "read",   txnId |-> 2, key |-> "k1", val |-> "Empty"],

    \* T0 writes k1 and k2, commits first
    [type |-> "write",  txnId |-> 0, key |-> "k1", val |-> "v1"],
    [type |-> "write",  txnId |-> 0, key |-> "k2", val |-> "v1"],
    [type |-> "commit", txnId |-> 0, time |-> 4, updatedKeys |-> {"k1", "k2"}],

    \* T1 writes k2 after T0 (creates T0→WW T1) and k3
    [type |-> "write",  txnId |-> 1, key |-> "k2", val |-> "v2"],
    [type |-> "write",  txnId |-> 1, key |-> "k3", val |-> "v1"],
    [type |-> "commit", txnId |-> 1, time |-> 5, updatedKeys |-> {"k2", "k3"}],

    \* T2 writes k3 after T1 (creates T1→WW T2) - k1 write creates T2→RW T0
    [type |-> "write",  txnId |-> 2, key |-> "k3", val |-> "v2"],
    [type |-> "commit", txnId |-> 2, time |-> 6, updatedKeys |-> {"k3"}]
>>


GSingle4NodeCycleTest == <<
    [type |-> "begin",  txnId |-> 0, time |-> 1],
    [type |-> "begin",  txnId |-> 1, time |-> 2], 
    [type |-> "begin",  txnId |-> 2, time |-> 3],
    
    \* T2 reads k1 early (for T2→RW T0)
    [type |-> "read",   txnId |-> 2, key |-> "k1", val |-> "Empty"],
    
    \* T0 writes k2 and k1, commits once
    [type |-> "write",  txnId |-> 0, key |-> "k2", val |-> "v1"],
    [type |-> "write",  txnId |-> 0, key |-> "k1", val |-> "v1"],
    [type |-> "commit", txnId |-> 0, time |-> 4, updatedKeys |-> {"k2", "k1"}],
    
    \* T3 begins AFTER T0 commits (for T0→WR T3)
    [type |-> "begin",  txnId |-> 3, time |-> 5],
    [type |-> "read",   txnId |-> 3, key |-> "k2", val |-> "v1"],
    [type |-> "write",  txnId |-> 3, key |-> "k3", val |-> "v1"],
    [type |-> "commit", txnId |-> 3, time |-> 6, updatedKeys |-> {"k3"}],
    
    \* T1 writes k3 after T3 commits (creates T3→WW T1)
    [type |-> "write",  txnId |-> 1, key |-> "k3", val |-> "v2"],
    [type |-> "write",  txnId |-> 1, key |-> "k4", val |-> "v1"],
    [type |-> "commit", txnId |-> 1, time |-> 7, updatedKeys |-> {"k3", "k4"}],
    
    \* T2 writes k4 after T1 commits (creates T1→WW T2)
    [type |-> "write",  txnId |-> 2, key |-> "k4", val |-> "v3"],
    [type |-> "commit", txnId |-> 2, time |-> 8, updatedKeys |-> {"k4"}]
>>


GNonadjacent4NodeTest == <<
    [type |-> "begin",  txnId |-> 3, time |-> 1], \* T3 begins
    [type |-> "read",   txnId |-> 3, key |-> "k1", val |-> "Empty"], \* T3 reads k1=0
    [type |-> "write",  txnId |-> 3, key |-> "k5", val |-> "v2"], \* T3 writes k5=v2
    [type |-> "begin",  txnId |-> 1, time |-> 2], \* T1 begins
    [type |-> "write",  txnId |-> 1, key |-> "k6", val |-> "v1"], \* T1 writes k6=v1
    [type |-> "begin",  txnId |-> 2, time |-> 3], \* T2 begins
    [type |-> "write",  txnId |-> 1, key |-> "k2", val |-> "v1"], \* T2 writes k2=v1
    [type |-> "write",  txnId |-> 3, key |-> "k3", val |-> "v2"], \* T2 writes k3=v2
    [type |-> "read",   txnId |-> 3, key |-> "k4", val |-> "Empty"], \* T3 reads k4=0
    [type |-> "commit", txnId |-> 1, time |-> 4, updatedKeys |-> {}], \* T1 commits
    [type |-> "begin",  txnId |-> 0, time |-> 5], \* T0 begins
    [type |-> "read",   txnId |-> 0, key |-> "k6", val |-> "v1"], \* T0 reads k6=v1
    [type |-> "write",  txnId |-> 2, key |-> "k5", val |-> "v1"], \* T2 writes k5=v1
    [type |-> "read",   txnId |-> 2, key |-> "k6", val |-> "Empty"], \* T2 reads k6=Empty
    [type |-> "commit", txnId |-> 3, time |-> 6, updatedKeys |-> {}], \* T2 commits
    [type |-> "read", txnId |-> 0, key |-> "k3", val |-> "Empty"], \* T0 reads k3=Empty
    [type |-> "commit", txnId |-> 2, time |-> 7, updatedKeys |-> {}], \* T0 commits
    [type |-> "commit", txnId |-> 0, time |-> 8, updatedKeys |-> {}] \* T0 commits
>>


GNonadjacent4NodeWithoutWWTest == <<
    [type |-> "begin",  txnId |-> 1, time |-> 1], \* T1 begins
    [type |-> "write",  txnId |-> 1, key |-> "X", val |-> "$50"], \* T1 writes (X, $50)
    [type |-> "write",  txnId |-> 1, key |-> "Y", val |-> "$50"], \* T1 writes (Y, $50) 
    [type |-> "write",  txnId |-> 1, key |-> "M", val |-> "Open"], \* T1 writes (M, "Open")
    [type |-> "commit", txnId |-> 1, time |-> 2, updatedKeys |-> {"X", "Y", "M"}], \* T1 commits
    [type |-> "begin",  txnId |-> 4, time |-> 3], \* T4 begins
    [type |-> "read",   txnId |-> 4, key |-> "M", val |-> "Open"], \* T4 reads M → gets "Open"
    [type |-> "begin",  txnId |-> 5, time |-> 4], \* T5 begins
    [type |-> "read",   txnId |-> 5, key |-> "M", val |-> "Open"], \* T5 reads M → gets "Open"
    [type |-> "begin",  txnId |-> 2, time |-> 5], \* Ta begins (renaming T2 to Ta for clarity)
    [type |-> "write",  txnId |-> 4, key |-> "X", val |-> "$70"], \* T4 writes (X, $70)
    [type |-> "commit", txnId |-> 4, time |-> 6, updatedKeys |-> {"X"}], \* T4 commits
    [type |-> "read",   txnId |-> 2, key |-> "X", val |-> "$70"], \* Ta reads X → gets $70 (sees T4's committed update)
    [type |-> "begin",  txnId |-> 3, time |-> 7], \* Tb begins (using txnId 3 for Tb)
    [type |-> "write",  txnId |-> 5, key |-> "Y", val |-> "$75"], \* T5 writes (Y, $75)
    [type |-> "read",   txnId |-> 2, key |-> "Y", val |-> "$50"], \* Ta reads Y → gets $50 (misses T5's update - T5 hasn't committed yet)
    [type |-> "commit", txnId |-> 2, time |-> 8, updatedKeys |-> {}], \* Ta commits
    [type |-> "commit", txnId |-> 5, time |-> 9, updatedKeys |-> {"Y"}], \* T5 commits
    [type |-> "read",   txnId |-> 3, key |-> "Y", val |-> "$75"], \* Tb reads Y → gets $75 (sees T5's committed update)
    [type |-> "read",   txnId |-> 3, key |-> "X", val |-> "$50"], \* Tb reads X → gets $50 (misses T4's update due to snapshot choice)
    [type |-> "commit", txnId |-> 3, time |-> 10, updatedKeys |-> {}] \* Tb commits
>>


G6NodeCycleTest == <<
    [type |-> "begin",  txnId |-> 0, time |-> 1],
    [type |-> "begin",  txnId |-> 1, time |-> 2],
    [type |-> "begin",  txnId |-> 2, time |-> 3],
    [type |-> "begin",  txnId |-> 3, time |-> 4],
    [type |-> "begin",  txnId |-> 4, time |-> 5],
    [type |-> "begin",  txnId |-> 5, time |-> 6],

    \* T0 writes k1 (for T0→WR T1)
    [type |-> "write",  txnId |-> 0, key |-> "k1", val |-> "v1"],
    
    \* T1 reads k1 from T0 (creates T0→WR T1)
    [type |-> "read",   txnId |-> 1, key |-> "k1", val |-> "v1"],
    
    \* T2 reads k2 early (for T1→RW T2)
    [type |-> "read",   txnId |-> 2, key |-> "k2", val |-> "Empty"],
    
    \* T1 writes k2 after T2 read (creates T1→RW T2)
    [type |-> "write",  txnId |-> 1, key |-> "k2", val |-> "v1"],
    
    \* T2 writes k3 (for T2→WR T3, since WW doesn't create edges)
    [type |-> "write",  txnId |-> 2, key |-> "k3", val |-> "v1"],
    
    \* T3 reads k3 from T2 (creates T2→WR T3)
    [type |-> "read",   txnId |-> 3, key |-> "k3", val |-> "v1"],
    
    \* T3 writes k4 (for T3→WR T4)
    [type |-> "write",  txnId |-> 3, key |-> "k4", val |-> "v1"],
    
    \* T4 reads k4 from T3 (creates T3→WR T4)
    [type |-> "read",   txnId |-> 4, key |-> "k4", val |-> "v1"],
    
    \* T5 reads k5 early (for T4→RW T5)
    [type |-> "read",   txnId |-> 5, key |-> "k5", val |-> "Empty"],
    
    \* T4 writes k5 after T5 read (creates T4→RW T5)
    [type |-> "write",  txnId |-> 4, key |-> "k5", val |-> "v1"],
    
    \* T5 writes k6 (for T5→WR T0, to close the cycle)
    [type |-> "write",  txnId |-> 5, key |-> "k6", val |-> "v1"],
    
    \* T0 reads k6 from T5 (creates T5→WR T0, completing the cycle)
    [type |-> "read",   txnId |-> 0, key |-> "k6", val |-> "v1"],
    
    \* Commits in order
    [type |-> "commit", txnId |-> 0, time |-> 7, updatedKeys |-> {"k1"}],
    [type |-> "commit", txnId |-> 1, time |-> 8, updatedKeys |-> {"k2"}],
    [type |-> "commit", txnId |-> 2, time |-> 9, updatedKeys |-> {"k3"}],
    [type |-> "commit", txnId |-> 3, time |-> 10, updatedKeys |-> {"k4"}],
    [type |-> "commit", txnId |-> 4, time |-> 11, updatedKeys |-> {"k5"}],
    [type |-> "commit", txnId |-> 5, time |-> 12, updatedKeys |-> {"k6"}]
>>

(**************************************************************************************************)
(* G-Single and G-Nonadjacent Anomaly (Experimental).                                             *)
(*                                                                                                *)
(* G-Single anomaly is where there is a dependency cycle of any length that contains exactly      *)
(* one RW edge. This is a specific type of non-serializable schedule that can occur under         *)
(* snapshot isolation.                                                                            *)
(**************************************************************************************************)

\* Returns TRUE if there is a simple cycle of length 3 in the edge set
Nodes(edges) == {e[1] : e \in edges} \cup {e[2] : e \in edges}


\* Returns TRUE if there is a simple cycle of length 2 in the edge set
Has2NodeCycle(edges) ==
    LET edgePairs == {<<e[1], e[2]>> : e \in edges}
    IN \E a \in Nodes(edges) :
         \E b \in Nodes(edges) :
           /\ a /= b
           /\ <<a, b>> \in edgePairs
           /\ <<b, a>> \in edgePairs
           /\ Cardinality({p \in edgePairs : p = <<a, b>>}) = 1
           /\ Cardinality({p \in edgePairs : p = <<b, a>>}) = 1

\* Returns TRUE if there is a simple cycle of length 3 in the edge set
Has3NodeCycle(edges) ==
    \* LET edgePairs == {<<e[1], e[2]>> : e \in edges}
    \E a \in Nodes(edges) :
         \E b \in Nodes(edges) :
           \E c \in Nodes(edges) :
          /\ a /= b /\ b /= c /\ c /= a
          /\ <<a, b>> \in edges
          /\ <<b, c>> \in edges
          /\ <<c, a>> \in edges
        \*   /\ Cardinality({p \in edgePairs : p = <<a, b>>}) = 1
        \*   /\ Cardinality({p \in edgePairs : p = <<b, c>>}) = 1
        \*   /\ Cardinality({p \in edgePairs : p = <<c, a>>}) = 1

\* Returns the serialization graph with edge types.
SerializationGraphWithEdgeTypes(history) == 
    LET committedTxnIds == CommittedTxns(history) IN
    {<<t1, t2, edgeType>> \in (committedTxnIds \X committedTxnIds \X {"WW", "WR", "RW"}):
        /\ t1 /= t2
        /\ \/ (edgeType = "WW" /\ WWDependency(history, t1, t2))
           \/ (edgeType = "WR" /\ WRDependency(history, t1, t2))
           \/ (edgeType = "RW" /\ RWDependency(history, t1, t2))}

\* Returns the serialization graph with edge types and concurrency information.
\* Output format: <<t1, t2, edgeType, concurrent_or_not>>
SerializationGraphWithCC(history) == 
    LET committedTxnIds == CommittedTxns(history) IN
    {<<t1, t2, edgeType, cclabel>> \in (committedTxnIds \X committedTxnIds \X {"WW", "WR", "RW"} \X {"concurrent", "not_concurrent"}):
        /\ t1 /= t2
        /\ \/ (edgeType = "WW" /\ WWDependency(history, t1, t2))
           \/ (edgeType = "WR" /\ WRDependency(history, t1, t2))
           \/ (edgeType = "RW" /\ RWDependency(history, t1, t2))
        /\ cclabel = IF AreConcurrent(history, t1, t2) THEN "concurrent" ELSE "not_concurrent"}

\* Returns the set of 2-node cycles found in the edge set
\* Each cycle is represented as a set of 2 nodes {a, b}
Find2NodeCycles(edges) ==
    LET nodeSet == Nodes(edges)
    IN { <<a, b>> \in (nodeSet \X nodeSet):
        /\ a /= b
        /\ <<a, b>> \in edges
        /\ <<b, a>> \in edges }

\* Returns the first 3-node cycle found (for debugging/display purposes)
First2NodeCycle(edges) ==
    CHOOSE cycle \in Find2NodeCycles(edges) : TRUE


HasSingleRWEdge(edges) ==
    LET simpleEdges == {<<e[1], e[2]>> : e \in edges}
    IN \E a \in Nodes(edges) :
         \E b \in Nodes(edges) :
           /\ a /= b
           /\ <<a, b>> \in simpleEdges
           /\ <<b, a>> \in simpleEdges
           /\ Cardinality({e \in edges : 
                              /\ (<<e[1], e[2]>> = <<a, b>> \/ <<e[1], e[2]>> = <<b, a>>)
                              /\ e[3] = "RW"}) = 1

\* 3 node cycle with one RW edge, one WR edge, and one WW edge
GSingleInv3NodeCycleAllEdges == 
    ~(
      /\ ~Has2NodeCycle(SerializationGraph(txnHistory))
      /\ Cardinality(SerializationGraphWithEdgeTypes(txnHistory)) <= 3
      /\ Cardinality(FindAllNodesInAnyCycle(SerializationGraph(txnHistory))) = 3
      /\ \E a,b,c \in FindAllNodesInAnyCycle(SerializationGraph(txnHistory)) :
        /\ Cardinality({a,b,c}) = 3
        \* /\ <<a, b, "RW">> \in SerializationGraphWithEdgeTypes(txnHistory)
        \* /\ <<b, c, "WR">> \in SerializationGraphWithEdgeTypes(txnHistory)
        \* /\ <<c, a, "WW">> \in SerializationGraphWithEdgeTypes(txnHistory)
    )

\* 3 node cycle with one RW edge and two WW edges
GSingleInv3NodeCycleOnlyRWWR == 
    ~(
      /\ Cardinality(SerializationGraphWithEdgeTypes(txnHistory)) <= 3
      /\ Cardinality(FindAllNodesInAnyCycle(SerializationGraph(txnHistory))) = 3
      /\ \E a,b,c \in FindAllNodesInAnyCycle(SerializationGraph(txnHistory)) :
        /\ Cardinality({a,b,c}) = 3
        /\ <<a, b, "RW">> \in SerializationGraphWithEdgeTypes(txnHistory)
        /\ <<b, c, "WR">> \in SerializationGraphWithEdgeTypes(txnHistory)
        /\ <<c, a, "WR">> \in SerializationGraphWithEdgeTypes(txnHistory)
    )

\* 3 node cycle with exactly one RW edge, one WW edge, and one WR edge
ThreeNodeCycle == 
    ~(
      /\ Cardinality(SerializationGraphWithEdgeTypes(txnHistory)) = 3
      /\ Cardinality(FindAllNodesInAnyCycle(SerializationGraph(txnHistory))) = 3
      /\ \E a,b,c \in FindAllNodesInAnyCycle(SerializationGraph(txnHistory)) :
        /\ Cardinality({a,b,c}) = 3
        \* /\ <<a, b, "RW">> \in SerializationGraphWithEdgeTypes(txnHistory)
        \* /\ <<b, c, "WW">> \in SerializationGraphWithEdgeTypes(txnHistory)
        \* /\ <<c, a, "WW">> \in SerializationGraphWithEdgeTypes(txnHistory)
    )


\* 2 node cycle with one RW edge and one WW edge using tracked edges
GSingle2Inv2NodeCycleRWWW == 
    LET \* Create simple graph edges for cycle detection (just <<src, dst>> pairs)
        simpleEdges == {<<src, dst>> : <<src, dst, edgeType, cclabel>> \in TrackedSerializationGraph}
        \* Extract just the edge type information for pattern matching
        typedEdges == {<<src, dst, edgeType>> : <<src, dst, edgeType, cclabel>> \in TrackedSerializationGraph}
    IN
    ~(
      /\ Cardinality(TrackedSerializationGraph) <= 2
      /\ Cardinality(FindAllNodesInAnyCycle(simpleEdges)) = 2
      /\ \E a,b \in FindAllNodesInAnyCycle(simpleEdges) :
        /\ Cardinality({a,b}) = 2
        /\ <<a, b, "RW">> \in typedEdges
        /\ <<b, a, "WW">> \in typedEdges
    )

GNonadjacentInv4NodeCycle2WR == 
    ~(
      /\ Cardinality(SerializationGraphWithEdgeTypes(txnHistory)) <= 4
      /\ Cardinality(FindAllNodesInAnyCycle(SerializationGraph(txnHistory))) = 4
      /\ \E a,b,c,d \in FindAllNodesInAnyCycle(SerializationGraph(txnHistory)) :
        /\ Cardinality({a,b,c,d}) = 4
        /\ <<a, b, "RW">> \in SerializationGraphWithEdgeTypes(txnHistory)
        /\ <<b, c, "WR">> \in SerializationGraphWithEdgeTypes(txnHistory)
        /\ <<c, d, "WR">> \in SerializationGraphWithEdgeTypes(txnHistory)
        /\ <<d, a, "WW">> \in SerializationGraphWithEdgeTypes(txnHistory)
    )
    
GNonadjacentInv4NodeCycleWRRW == 
    ~(
      /\ Cardinality(SerializationGraphWithEdgeTypes(txnHistory)) <= 4
      /\ Cardinality(FindAllNodesInAnyCycle(SerializationGraph(txnHistory))) = 4
      /\ \E a,b,c,d \in FindAllNodesInAnyCycle(SerializationGraph(txnHistory)) :
        /\ Cardinality({a,b,c,d}) = 4
        /\ <<a, b, "RW">> \in SerializationGraphWithEdgeTypes(txnHistory)
        /\ \E ty \in {"WR", "WW"} : <<b, c, ty>> \in SerializationGraphWithEdgeTypes(txnHistory)
        /\ \E ty \in {"WR", "WW"} : <<c, d, ty>> \in SerializationGraphWithEdgeTypes(txnHistory)
        /\ <<d, a, "WR">> \in SerializationGraphWithEdgeTypes(txnHistory)
    )

GNonadjacentInv5NodeCycle == 
    ~(
      /\ Cardinality(SerializationGraphWithEdgeTypes(txnHistory)) <= 5
      /\ Cardinality(FindAllNodesInAnyCycle(SerializationGraph(txnHistory))) = 5
      /\ \E a,b,c,d,e \in FindAllNodesInAnyCycle(SerializationGraph(txnHistory)) :
        /\ Cardinality({a,b,c,d,e}) = 5
        /\ <<a, b, "RW">> \in SerializationGraphWithEdgeTypes(txnHistory)
        /\ \E ty \in {"WR", "WW"} : <<b, c, ty>> \in SerializationGraphWithEdgeTypes(txnHistory)
        /\ \E ty \in {"WR", "WW"} : <<c, d, ty>> \in SerializationGraphWithEdgeTypes(txnHistory)
        /\ \E ty \in {"WR", "WW"} : <<d, e, ty>> \in SerializationGraphWithEdgeTypes(txnHistory)
        /\ \E ty \in {"WR", "WW"} : <<e, a, ty>> \in SerializationGraphWithEdgeTypes(txnHistory)
    )

GNonadjacentInv6NodeCycle == 
    ~(
      /\ Cardinality(SerializationGraphWithEdgeTypes(txnHistory)) <= 6
      /\ Cardinality(FindAllNodesInAnyCycle(SerializationGraph(txnHistory))) = 6
      /\ \E a,b,c,d,e,f \in FindAllNodesInAnyCycle(SerializationGraph(txnHistory)) :
        /\ Cardinality({a,b,c,d,e,f}) = 6
        /\ <<a, b, "RW">> \in SerializationGraphWithEdgeTypes(txnHistory)
        /\ \E ty \in {"WR", "WW"} : <<b, c, ty>> \in SerializationGraphWithEdgeTypes(txnHistory)
        /\ <<c, d, "RW">> \in SerializationGraphWithEdgeTypes(txnHistory)
        /\ \E ty \in {"WR", "WW"} : <<d, e, ty>> \in SerializationGraphWithEdgeTypes(txnHistory)
        /\ \E ty \in {"WR", "WW"} : <<e, f, ty>> \in SerializationGraphWithEdgeTypes(txnHistory)
        /\ \E ty \in {"WR", "WW"} : <<f, a, ty>> \in SerializationGraphWithEdgeTypes(txnHistory)
    )

\* ASSUME 
\*     PrintT(SerializationGraphWithCC(G6NodeCycleTest))
\* /\ \E ty \in {"WR", "WW"} : <<d, a, ty>> \in SerializationGraphWithEdgeTypes(txnHistory)

Invariant == GSingle2Inv2NodeCycleRWWW


\* Find the cardinality of a given edge pair in the edge set
FindCardinality(edges, pair) ==
    Cardinality({e \in edges : <<e[1], e[2]>> = pair})

\* Cardinality check for the actual transaction history (txnHistory)
TxnHistoryCardinality(h) == 
    LET detailedEdges == SerializationGraphWithEdgeTypes(h)
        \* Extract just the node pairs (ignoring edge types) for cardinality checking
        edgePairs == {<<e[1], e[2]>> : e \in detailedEdges}
    IN [pair \in edgePairs |-> FindCardinality(detailedEdges, pair)]


\* For debugging within the model checker in VSCode
Alias == [
    txnHistory |-> txnHistory,
    ccgraph |-> TrackedSerializationGraph,
    incomingEdges |-> incomingEdges,
    outgoingEdges |-> outgoingEdges
    \* isCycle |-> IsCycle(SerializationGraph(txnHistory)),
    \* nodesSet |-> First2NodeCycle(SerializationGraph(txnHistory))
    \* edgeCardinalities |-> TxnHistoryCardinality(txnHistory)
]


-------------------------------------------------

\* Some model checking details.

Symmetry == Permutations(keys) \cup Permutations(values) \cup Permutations(txnIds)

-------------------------------------------------


\* 
\* Animation stuff.
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

\* Rectangle element. 'x', 'y', 'w', and 'h' should be given as integers.
Rect(x, y, w, h, attrs) == 
    LET svgAttrs == [x      |-> x, 
                     y      |-> y, 
                     width  |-> w, 
                     height |-> h] IN
    SVGElem("rect", Merge(svgAttrs, attrs), <<>>, "")

Image(x, y, width, height, href, attrs) == 
    LET svgAttrs == ("xlink:href" :> href @@
                     "x"         :> x @@
                     "y"         :> y @@
                     "width"     :> width @@
                     "height"    :> height) IN
    SVGElem("image", Merge(svgAttrs, attrs), <<>>, "")

\* Group element. 'children' is as a sequence of elements that will be contained in this group.
Group(children, attrs) == SVGElem("g", attrs, children, "")

\* Edges can also be specified as tuples of length > 2, such as <<n1,n2,x,y,z>>,
\* which defines an edge between n1 -> n2, but x,y,z define additional metadata
\* specific to that edge e.g. this also allows for multiple edges between the
\* same nodes in the same direction, but with potentially different edge
\* "types".
DiGraph(V, E, nodeAttrsFn, edgeAttrsFn) == SVGElem("digraph", [V |-> V, E |-> E, nodeAttrsFn |-> nodeAttrsFn, edgeAttrsFn |-> edgeAttrsFn], <<>>, "")

Injective(f) == \A x, y \in DOMAIN f : f[x] = f[y] => x = y

\* Establish a fixed mapping to assign an ordering to elements in these sets.
\* ServerId == CHOOSE f \in [Server -> 1..Cardinality(Person)] : Injective(f)
\* RMId == CHOOSE f \in [1..Cardinality(Server) -> Server] : Injective(f)
\* SetToSeq(S) == CHOOSE f \in [1..Cardinality(S) -> S] : Injective(f)
\* RMId == SetToSeq(Server)
\* CHOOSE f \in [1..Cardinality(Server) -> Server] : Injective(f)

\* Graphviz attributes
nodeAttrsFn(n) == [
    label |-> ToString(n),
    style |-> "filled", 
    fillcolor |-> IF n \in CommittedTxns(txnHistory) THEN "lightgreen" ELSE "lightgray"
]

edgeAttrsFn(e) == [
    label |-> e[3],
    color |-> "black",
    fontsize |-> "8"
]

txnGraph == SerializationGraph(txnHistory)

allCommittedTxnIds == CommittedTxns(txnHistory)

\* Alternate def of above.
txnGraphWithEdgeTypes == 
    {e \in (allCommittedTxnIds \X allCommittedTxnIds \X {"WW", "WR", "RW"}):
        /\ e[1][1] /= e[1][2]
        /\ \/ (e[2] = "WW" /\ WWDependency(txnHistory, e[1][1], e[1][2]))
           \/ (e[2] = "WR" /\ WRDependency(txnHistory, e[1][1], e[1][2]))
           \/ (e[2] = "RW" /\ RWDependency(txnHistory, e[1][1], e[1][2]))}
txnGraphEdges == {<<e[1][1], e[1][2], e[2]>> : e \in txnGraphWithEdgeTypes}
AnimView == Group(<<DiGraph(txnIds,txnGraphEdges,[n \in txnIds |-> nodeAttrsFn(n)], [e \in txnGraphEdges |-> edgeAttrsFn(e)])>>, [i \in {} |-> {}])

=============================================================================
\* Modification History
\* Last modified Tue Feb 27 12:56:09 EST 2018 by williamschultz
\* Created Sat Jan 13 08:59:10 EST 2018 by williamschultz

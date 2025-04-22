--------------------------------- MODULE AsyncRaft ---------------------------------

\* 
\* 
\* Specification of Raft with message passing.
\* 
\* Original source: https://github.com/Vanlightly/raft-tlaplus/blob/main/specifications/standard-raft/Raft.tla
\* Modified by Will Schultz for safety proof experiments, August 2023.
\* 
\* 

\* EXTENDS Naturals, FiniteSets, FiniteSetsExt, Sequences, Bags, TLC
EXTENDS Naturals, FiniteSets, Sequences, TLC
\* , Randomization

\* The set of server IDs
CONSTANTS 
    \* @typeAlias: SERVER = Str;
    \* @type: Set(SERVER);
    Server

\* Server states.
CONSTANTS 
    \* @type: Str;
    Follower, 
    \* @type: Str;
    Candidate, 
    \* @type: Str;
    Leader

\* A reserved value.
CONSTANTS 
    \* @type: Str;
    Nil

\* Message types:
CONSTANTS 
    \* @type: Str;
    RequestVoteRequest, 
    \* @type: Str;
    RequestVoteResponse,
    \* @type: Str;
    AppendEntriesRequest, 
    \* @type: Str;
    AppendEntriesResponse

----
\* Global variables.

VARIABLE 
    \* @type: Set({ mtype: Str, mterm: Int, mlastLogTerm: Int, mlastLogIndex: Int, msource: SERVER, mdest: SERVER });
    requestVoteRequestMsgs

VARIABLE 
    \* @type: Set({ mtype: Str, mterm: Int, mvoteGranted: Bool, msource: SERVER, mdest: SERVER });
    requestVoteResponseMsgs

VARIABLE 
    \* @type: Set({ mtype: Str, mterm: Int, mprevLogIndex: Int, mprevLogTerm: Int, mentries: Seq(Int), mcommitIndex: Int, msource: SERVER, mdest: SERVER });
    appendEntriesRequestMsgs

VARIABLE 
    \* @type: Set({ mtype: Str, mterm: Int, msuccess: Bool, mmatchIndex: Int, msource: SERVER, mdest: SERVER });
    appendEntriesResponseMsgs

----
\* Auxilliary variables (used for state-space control, invariants etc)

\* The server's term number.
VARIABLE 
    \* @type: SERVER -> Int; 
    currentTerm

\* The server's state (Follower, Candidate, or Leader).
VARIABLE 
    \* @type: SERVER -> Str; 
    state

\* The candidate the server voted for in its current term, or
\* Nil if it hasn't voted for any.
VARIABLE 
    \* @type: SERVER -> SERVER;
    votedFor

\* A Sequence of log entries. The index into this sequence is the index of the
\* log entry. Unfortunately, the Sequence module defines Head(s) as the entry
\* with index 1, so be careful not to use that!
VARIABLE 
    \* @type: SERVER -> Seq(Int);
    log

\* The index of the latest entry in the log the state machine may apply.
VARIABLE 
    \* @type: SERVER -> Int;
    commitIndex


\* The following variables are used only on candidates:

\* The set of servers from which the candidate has received a vote in its
\* currentTerm.
VARIABLE 
    \* @type: SERVER -> Set(SERVER);
    votesGranted


\* The following variables are used only on leaders:
\* The next entry to send to each follower.
VARIABLE
    \* @type: SERVER -> (SERVER -> Int);
    nextIndex

\* The latest entry that each follower has acknowledged is the same as the
\* leader's. This is used to calculate commitIndex on the leader.
VARIABLE 
    \* @type: SERVER -> (SERVER -> Int);
    matchIndex


serverVars == <<currentTerm, state, votedFor>>
logVars == <<log, commitIndex>>

\* End of per server variables.-

\* All variables; used for stuttering (asserting state hasn't changed).
vars == <<requestVoteRequestMsgs, requestVoteResponseMsgs, appendEntriesRequestMsgs, appendEntriesResponseMsgs, currentTerm, state, votedFor, votesGranted, nextIndex, matchIndex, log, commitIndex>>

\* Helpers

Min(s) == CHOOSE x \in s : \A y \in s : x <= y
Max(s) == CHOOSE x \in s : \A y \in s : x >= y

\* The set of all quorums. This just calculates simple majorities, but the only
\* important property is that every quorum overlaps with every other.
Quorum == {i \in SUBSET(Server) : Cardinality(i) * 2 > Cardinality(Server)}

\* The term of the last entry in a log, or 0 if the log is empty.
LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)]

IsPrefix(s, t) ==
  (**************************************************************************)
  (* TRUE iff the sequence s is a prefix of the sequence t, s.t.            *)
  (* \E u \in Seq(Range(t)) : t = s \o u. In other words, there exists      *)
  (* a suffix u that with s prepended equals t.                             *)
  (**************************************************************************)
  Len(s) <= Len(t) /\ SubSeq(s, 1, Len(s)) = SubSeq(t, 1, Len(s))
  
----
\* Define initial values for all variables

\* InitcurrentTerm, state, votedFor == /\ currentTerm = [i \in Server |-> 1]
\*                   /\ state       = [i \in Server |-> Follower]
\*                   /\ votedFor    = [i \in Server |-> Nil]
\* InitCandidateVars == votesGranted   = [i \in Server |-> {}]
\* \* The values nextIndex[i][i] and matchIndex[i][i] are never read, since the
\* \* leader does not send itself messages. It's still easier to include these
\* \* in the functions.
\* InitLeaderVars == /\ nextIndex  = [i \in Server |-> [j \in Server |-> 1]]
\*                   /\ matchIndex = [i \in Server |-> [j \in Server |-> 0]]
\* Initlog, commitIndex == /\ log             = [i \in Server |-> << >>]
\*                /\ commitIndex     = [i \in Server |-> 0]

Init == 
    /\ requestVoteRequestMsgs = {}
    /\ requestVoteResponseMsgs = {}
    /\ appendEntriesRequestMsgs = {}
    /\ appendEntriesResponseMsgs = {}
    /\ currentTerm = [i \in Server |-> 0]
    /\ state       = [i \in Server |-> Follower]
    /\ votedFor    = [i \in Server |-> Nil]
    /\ votesGranted = [i \in Server |-> {}]
    /\ nextIndex  = [i \in Server |-> [j \in Server |-> 1]]
    /\ matchIndex = [i \in Server |-> [j \in Server |-> 0]]        
    /\ log             = [i \in Server |-> << >>]
    /\ commitIndex     = [i \in Server |-> 0]
    
----
\* Define state transitions

\* ACTION: Restart -------------------------------------
\* Server i restarts from stable storage.
\* It loses everything but its currentTerm, votedFor and log.
Restart(i) ==
    /\ state'           = [state EXCEPT ![i] = Follower]
    /\ votesGranted'    = [votesGranted EXCEPT ![i] = {}]
    /\ nextIndex'       = [nextIndex EXCEPT ![i] = [j \in Server |-> 1]]
    /\ matchIndex'      = [matchIndex EXCEPT ![i] = [j \in Server |-> 0]]
    /\ commitIndex'     = [commitIndex EXCEPT ![i] = 0]
    /\ UNCHANGED <<currentTerm, votedFor, log, requestVoteRequestMsgs, requestVoteResponseMsgs, appendEntriesRequestMsgs, appendEntriesResponseMsgs>>

\* ACTION: RequestVote
\* Combined Timeout and RequestVote of the original spec to reduce
\* state space.
\* Server i times out and starts a new election. 
\* Sends a RequestVote request to all peers but not itself.
RequestVote(i) ==
    /\ state[i] \in {Follower, Candidate}
    /\ state' = [state EXCEPT ![i] = Candidate]
    /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
    /\ votedFor' = [votedFor EXCEPT ![i] = i] \* votes for itself
    /\ votesGranted'   = [votesGranted EXCEPT ![i] = {i}] \* votes for itself
    /\ requestVoteRequestMsgs' = requestVoteRequestMsgs \cup 
            {[  mtype         |-> RequestVoteRequest,
                mterm         |-> currentTerm[i] + 1,
                mlog |-> log[i],
                msource       |-> i,
                mdest         |-> j] : j \in Server \ {i}}
    /\ UNCHANGED <<nextIndex, matchIndex, log, commitIndex, appendEntriesRequestMsgs, appendEntriesResponseMsgs, requestVoteResponseMsgs>>

\* ACTION: AppendEntries ----------------------------------------
\* Leader i sends j an AppendEntries request containing up to 1 entry.
\* While implementations may want to send more than 1 at a time, this spec uses
\* just 1 because it minimizes atomic regions without loss of generality.
AppendEntries(i, j) ==
    /\ i /= j
    /\ state[i] = Leader
    /\ LET 
            \* prevLogIndex == nextIndex[i][j] - 1
        \*    prevLogTerm == IF (prevLogIndex > 0 /\ prevLogIndex \in DOMAIN log[i])
                            \* THEN log[i][prevLogIndex]
                            \* ELSE 0
           \* Send up to 1 entry, constrained by the end of the log.
           \* NOTE: This spec never sends more than one entry at a time currently. (Will S.)
           lastEntry == Min({Len(log[i]), nextIndex[i][j]})
        \*    entries == SubSeq(log[i], nextIndex[i][j], lastEntry)
       IN 
          /\ appendEntriesRequestMsgs' = appendEntriesRequestMsgs \cup {[
                   mtype          |-> AppendEntriesRequest,
                   mterm          |-> currentTerm[i],
                \*    mprevLogIndex  |-> prevLogIndex,
                \*    mprevLogTerm   |-> prevLogTerm,
                \*    mentries       |-> entries,
                   mlog           |-> log[i],
                   mcommitIndex   |-> Min({commitIndex[i], lastEntry}),
                   msource        |-> i,
                   mdest          |-> j]}
    /\ UNCHANGED <<currentTerm, state, votedFor, votesGranted, nextIndex, matchIndex, log, commitIndex, requestVoteRequestMsgs, requestVoteResponseMsgs, appendEntriesResponseMsgs>>

\* ACTION: BecomeLeader -------------------------------------------
\* Candidate i transitions to leader.
BecomeLeader(i) ==
    /\ state[i] = Candidate
    /\ votesGranted[i] \in Quorum
    /\ state'      = [state EXCEPT ![i] = Leader]
    /\ nextIndex'  = [nextIndex EXCEPT ![i] = [j \in Server |-> Len(log[i]) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![i] = [j \in Server |-> 0]]
    /\ UNCHANGED <<appendEntriesRequestMsgs, appendEntriesResponseMsgs, currentTerm, votedFor, votesGranted, log, commitIndex, requestVoteRequestMsgs, requestVoteResponseMsgs>>

\* ACTION: ClientRequest ----------------------------------
\* Leader i receives a client request to add v to the log.
ClientRequest(i) ==
    /\ state[i] = Leader
    /\ log' = [log EXCEPT ![i] = Append(log[i], currentTerm[i])]
    /\ UNCHANGED <<appendEntriesRequestMsgs, appendEntriesResponseMsgs, currentTerm, state, votedFor, votesGranted, nextIndex, matchIndex, commitIndex, requestVoteRequestMsgs, requestVoteResponseMsgs>>

\* The set of servers that agree up through index.
Agree(i, index) == {i} \cup {k \in Server : matchIndex[i][k] >= index }

\* ACTION: AdvanceCommitIndex ---------------------------------
\* Leader i advances its commitIndex.
\* This is done as a separate step from handling AppendEntries responses,
\* in part to minimize atomic regions, and in part so that leaders of
\* single-server clusters are able to mark entries committed.
AdvanceCommitIndex(i) ==
    /\ state[i] = Leader
    /\ LET \* The maximum indexes for which a quorum agrees
           agreeIndexes == {index \in DOMAIN log[i] : Agree(i, index) \in Quorum}
           \* New value for commitIndex'[i]
           newCommitIndex ==
              IF /\ agreeIndexes /= {}
                 /\ log[i][Max(agreeIndexes)] = currentTerm[i]
              THEN Max(agreeIndexes)
              ELSE commitIndex[i]
       IN 
          /\ commitIndex[i] < newCommitIndex \* only enabled if it actually advances
          /\ commitIndex' = [commitIndex EXCEPT ![i] = newCommitIndex]
    /\ UNCHANGED <<appendEntriesRequestMsgs, appendEntriesResponseMsgs, currentTerm, state, votedFor, votesGranted, nextIndex, matchIndex, log, requestVoteRequestMsgs, requestVoteResponseMsgs>>

UpdateTerm(m,mterm,mdest) ==
    /\ mterm > currentTerm[mdest]
    /\ m \in (requestVoteRequestMsgs \cup requestVoteResponseMsgs \cup appendEntriesRequestMsgs \cup appendEntriesResponseMsgs)
    /\ currentTerm'    = [currentTerm EXCEPT ![mdest] = mterm]
    /\ state'          = [state       EXCEPT ![mdest] = Follower]
    /\ votedFor'       = [votedFor    EXCEPT ![mdest] = Nil]
        \* messages is unchanged so m can be processed further.
    /\ UNCHANGED <<appendEntriesRequestMsgs, appendEntriesResponseMsgs, votesGranted, nextIndex, matchIndex, log, commitIndex, requestVoteRequestMsgs, requestVoteResponseMsgs>>


\* \* ACTION: UpdateTerm
\* \* Any RPC with a newer term causes the recipient to advance its term first.
\* UpdateTermRVReq(mterm,mdest) ==
\*     /\ mterm > currentTerm[mdest]
\*     /\ currentTerm'    = [currentTerm EXCEPT ![mdest] = mterm]
\*     /\ state'          = [state       EXCEPT ![mdest] = Follower]
\*     /\ votedFor'       = [votedFor    EXCEPT ![mdest] = Nil]
\*         \* messages is unchanged so m can be processed further.
\*     /\ UNCHANGED <<appendEntriesRequestMsgs, appendEntriesResponseMsgs, votesGranted, nextIndex, matchIndex, log, commitIndex, requestVoteRequestMsgs, requestVoteResponseMsgs>>

\* UpdateTermRVRes(mterm,mdest) ==
\*     /\ mterm > currentTerm[mdest]
\*     /\ currentTerm'    = [currentTerm EXCEPT ![mdest] = mterm]
\*     /\ state'          = [state       EXCEPT ![mdest] = Follower]
\*     /\ votedFor'       = [votedFor    EXCEPT ![mdest] = Nil]
\*         \* messages is unchanged so m can be processed further.
\*     /\ UNCHANGED <<appendEntriesRequestMsgs, appendEntriesResponseMsgs, votesGranted, nextIndex, matchIndex, log, commitIndex, requestVoteRequestMsgs, requestVoteResponseMsgs>>

\* UpdateTermAEReq(mterm,mdest) ==
\*     /\ mterm > currentTerm[mdest]
\*     /\ currentTerm'    = [currentTerm EXCEPT ![mdest] = mterm]
\*     /\ state'          = [state       EXCEPT ![mdest] = Follower]
\*     /\ votedFor'       = [votedFor    EXCEPT ![mdest] = Nil]
\*         \* messages is unchanged so m can be processed further.
\*     /\ UNCHANGED <<appendEntriesRequestMsgs, appendEntriesResponseMsgs, votesGranted, nextIndex, matchIndex, log, commitIndex, requestVoteRequestMsgs, requestVoteResponseMsgs>>

\* UpdateTermAERes(mterm,mdest) ==
\*     /\ mterm > currentTerm[mdest]
\*     /\ currentTerm'    = [currentTerm EXCEPT ![mdest] = mterm]
\*     /\ state'          = [state       EXCEPT ![mdest] = Follower]
\*     /\ votedFor'       = [votedFor    EXCEPT ![mdest] = Nil]
\*         \* messages is unchanged so m can be processed further.
\*     /\ UNCHANGED <<appendEntriesRequestMsgs, appendEntriesResponseMsgs, votesGranted, nextIndex, matchIndex, log, commitIndex, requestVoteRequestMsgs, requestVoteResponseMsgs>>



\* ACTION: HandleRequestVoteRequest ------------------------------
\* Server i receives a RequestVote request from server j with
\* m.mterm <= currentTerm[i].
\* @type: ({ mtype: Str, mterm: Int, mlastLogTerm: Int, mlastLogIndex: Int, msource: SERVER, mdest: SERVER }) => Bool;
HandleRequestVoteRequest(m) ==
    /\ m \in requestVoteRequestMsgs
    /\ m.mtype = RequestVoteRequest
    /\ m.mterm <= currentTerm[m.mdest]
    /\ LET  i     == m.mdest
            j     == m.msource
            logOk == \/ LastTerm(m.mlog) > LastTerm(log[i])
                     \/ /\ LastTerm(m.mlog) = LastTerm(log[i])
                        /\ Len(m.mlog) >= Len(log[i])
            grant == /\ m.mterm = currentTerm[i]
                     /\ logOk
                     /\ votedFor[i] \in {Nil, j} 
                     IN
            /\ votedFor' = [votedFor EXCEPT ![i] = IF grant THEN j ELSE votedFor[i]]
            /\ requestVoteResponseMsgs' = requestVoteResponseMsgs \cup {[
                            mtype        |-> RequestVoteResponse,
                            mterm        |-> currentTerm[i],
                            mvoteGranted |-> grant,
                            msource      |-> i,
                            mdest        |-> j]}
            /\ requestVoteRequestMsgs' = requestVoteRequestMsgs \* \ {m} \* discard the message.
            /\ UNCHANGED <<state, currentTerm, votesGranted, nextIndex, matchIndex, log, commitIndex, appendEntriesRequestMsgs, appendEntriesResponseMsgs>>

\* ACTION: HandleRequestVoteResponse --------------------------------
\* Server i receives a RequestVote response from server j with
\* m.mterm = currentTerm[i].
HandleRequestVoteResponse(m) ==
    \* This tallies votes even when the current state is not Candidate, but
    \* they won't be looked at, so it doesn't matter.
    /\ m \in requestVoteResponseMsgs
    /\ m.mtype = RequestVoteResponse
    /\ m.mterm = currentTerm[m.mdest]
    /\ votesGranted' = [votesGranted EXCEPT ![m.mdest] = 
                                IF m.mvoteGranted 
                                    THEN votesGranted[m.mdest] \cup {m.msource} 
                                    ELSE votesGranted[m.mdest]]
    \* /\ requestVoteResponseMsgs' = requestVoteResponseMsgs \* \ {m} \* discard the message.
    /\ UNCHANGED <<currentTerm, state, votedFor, nextIndex, matchIndex, log, commitIndex, appendEntriesRequestMsgs, appendEntriesResponseMsgs, requestVoteRequestMsgs, requestVoteResponseMsgs>>

\* ACTION: RejectAppendEntriesRequest -------------------
\* Either the term of the message is stale or the message
\* entry is too high (beyond the last log entry + 1)
\* @type: (SERVER, { mtype: Str, mterm: Int, mprevLogIndex: Int, mprevLogTerm: Int, mentries: Seq(Int), mcommitIndex: Int, msource: SERVER, mdest: SERVER }) => Bool;
LogOk(i, m) ==
    \/ m.mprevLogIndex = 0
    \/ /\ m.mprevLogIndex > 0
       /\ m.mprevLogIndex <= Len(log[i])
       /\ m.mprevLogTerm = log[i][m.mprevLogIndex]


\* @type: ({ mtype: Str, mterm: Int, mprevLogIndex: Int, mprevLogTerm: Int, mentries: Seq(Int), mcommitIndex: Int, msource: SERVER, mdest: SERVER }) => Bool;
RejectAppendEntriesRequest(m) ==
    /\ m.mtype = AppendEntriesRequest
    /\ m.mterm <= currentTerm[m.mdest]
    /\ LET  i     == m.mdest
            j     == m.msource
            logOk == LogOk(i, m)
        IN  /\ \/ m.mterm < currentTerm[i]
                \/ /\ m.mterm = currentTerm[i]
                   /\ state[i] = Follower
                   /\ \lnot logOk
            /\ appendEntriesResponseMsgs' = appendEntriesResponseMsgs \cup 
                {[
                        mtype           |-> AppendEntriesResponse,
                        mterm           |-> currentTerm[i],
                        msuccess        |-> FALSE,
                        mmatchIndex     |-> 0,
                        msource         |-> i,
                        mdest           |-> j]}
            /\ UNCHANGED <<state, votesGranted, nextIndex, matchIndex, currentTerm, state, votedFor, log, commitIndex, requestVoteRequestMsgs, requestVoteResponseMsgs, appendEntriesRequestMsgs>>

\* ACTION: AcceptAppendEntriesRequest ------------------
\* The original spec had to three sub actions, this version is compressed.
\* In one step it can:
\* - truncate the log
\* - append an entry to the log
\* - respond to the leader         
\* @type: ({ mtype: Str, mterm: Int, mprevLogIndex: Int, mprevLogTerm: Int, mentries: Seq(Int), mcommitIndex: Int, msource: SERVER, mdest: SERVER }, SERVER) => Bool;
CanAppend(m, i) ==
    /\ m.mentries /= << >>
    /\ Len(log[i]) = m.mprevLogIndex
    
\* truncate in two cases:
\* - the last log entry index is >= than the entry being received
\* - this is an empty RPC and the last log entry index is > than the previous log entry received
\* NeedsTruncation(m, i, index) ==
\*    \/ /\ m.mentries /= <<>>
\*       /\ Len(log[i]) >= index
\*    \/ /\ m.mentries = <<>>
\*       /\ Len(log[i]) > m.mprevLogIndex

TruncateLog(m, i) ==
    [index \in 1..m.mprevLogIndex |-> log[i][index]]

AcceptAppendEntriesRequestAppend(m) ==
    /\ m \in appendEntriesRequestMsgs
    /\ m.mtype = AppendEntriesRequest
    /\ m.mterm = currentTerm[m.mdest]
    /\ LET  i     == m.mdest
            j     == m.msource
            \* logOk == LogOk(i, m)
            \* index == m.mprevLogIndex + 1
        IN 
            /\ state[i] \in { Follower }
            \* /\ logOk
            /\ IsPrefix(log[i], m.mlog)
            \* /\ CanAppend(m, i)
            \* Only update the logs in this action. commit learning is done in a separate action.
            \* /\ log' = [log EXCEPT ![i] = Append(log[i], m.mentries[1])]
            /\ log' = [log EXCEPT ![i] = m.mlog]
            /\ appendEntriesResponseMsgs' = appendEntriesResponseMsgs \cup {[
                        mtype           |-> AppendEntriesResponse,
                        mterm           |-> currentTerm[i],
                        \* msuccess        |-> TRUE,
                        mlog            |-> log'[i],
                        \* mmatchIndex     |-> m.mprevLogIndex + Len(m.mentries),
                        msource         |-> i,
                        mdest           |-> j]}
            /\ UNCHANGED <<state, votesGranted, commitIndex, nextIndex, matchIndex, votedFor, currentTerm, requestVoteRequestMsgs, requestVoteResponseMsgs, appendEntriesRequestMsgs>>
       
AcceptAppendEntriesRequestTruncate(m) ==
    /\ m \in appendEntriesRequestMsgs
    /\ m.mtype = AppendEntriesRequest
    /\ m.mterm = currentTerm[m.mdest]
    /\ LET  i     == m.mdest
            j     == m.msource
            logOk == LogOk(i, m)
            index == m.mprevLogIndex + 1
        IN 
            /\ state[i] \in { Follower, Candidate }
            /\ logOk
            \* We only truncate if terms do not match and our log index
            \* is >= the log of the sender. Note that we do not reset the commitIndex
            \* here as well, since if safety holds, then we should never be truncating a 
            \* portion of the log that is covered by a commitIndex.
            /\ m.mentries # << >>
            /\ Len(log[i]) >= index
            /\ m.mentries[1] > log[i][index]
            /\ state' = [state EXCEPT ![i] = Follower]
            /\ log' = [log EXCEPT ![i] = TruncateLog(m, i)]
            /\ appendEntriesResponseMsgs' = appendEntriesResponseMsgs \cup {[
                        mtype           |-> AppendEntriesResponse,
                        mterm           |-> currentTerm[i],
                        msuccess        |-> TRUE,
                        mmatchIndex     |-> m.mprevLogIndex,
                        msource         |-> i,
                        mdest           |-> j]}
            /\ UNCHANGED <<votesGranted, nextIndex, matchIndex, commitIndex, votedFor, currentTerm, requestVoteRequestMsgs, requestVoteResponseMsgs, appendEntriesRequestMsgs>>

AcceptAppendEntriesRequestLearnCommit(m) ==
    /\ m \in appendEntriesRequestMsgs
    /\ m.mtype = AppendEntriesRequest
    /\ m.mterm = currentTerm[m.mdest]
    /\ LET  i     == m.mdest
            j     == m.msource
            \* logOk == LogOk(i, m)
        IN 
            /\ state[i] \in { Follower }
            \* We can learn a commitIndex as long as the log check passes, and if we could append these log entries.
            \* We will not, however, advance our local commitIndex to a point beyond the end of our log. And,
            \* we don't actually update our log here, only our commitIndex.

            \* /\ CanAppend(m, i)
            \* /\ logOk
            \* /\ Len(log[i]) = m.mprevLogIndex

            \* PRE (can comment these conditions out to introduce bug)
            /\ IsPrefix(log[i], m.mlog)

            /\ m.mcommitIndex > commitIndex[i] \* no need to ever decrement our commitIndex.
            /\ commitIndex' = [commitIndex EXCEPT ![i] = Min({m.mcommitIndex, Len(log[i])})]
            \* No need to send a response message since we are not updating our logs.
            /\ UNCHANGED <<state, votesGranted, appendEntriesRequestMsgs, appendEntriesResponseMsgs, nextIndex, matchIndex, log, votedFor, currentTerm, requestVoteRequestMsgs, requestVoteResponseMsgs>>


\* ACTION: HandleAppendEntriesResponse
\* Server i receives an AppendEntries response from server j with
\* m.mterm = currentTerm[i].
\* @type: ({ mtype: Str, mterm: Int, msuccess: Bool, mmatchIndex: Int, msource: SERVER, mdest: SERVER }) => Bool;
HandleAppendEntriesResponse(m) ==
    /\ m \in appendEntriesResponseMsgs
    /\ m.mtype = AppendEntriesResponse
    /\ m.mterm = currentTerm[m.mdest]
    /\ IsPrefix(m.mlog, log[m.mdest])
    /\ LET i     == m.mdest
           j     == m.msource
        IN
            \* /\ \/ /\ m.msuccess \* successful
            \*       /\ nextIndex'  = [nextIndex  EXCEPT ![i][j] = m.mmatchIndex + 1]
            \*       /\ matchIndex' = [matchIndex EXCEPT ![i][j] = m.mmatchIndex]
            \*    \/ /\ \lnot m.msuccess \* not successful
            \*       /\ nextIndex' = [nextIndex EXCEPT ![i][j] = Max({nextIndex[i][j] - 1, 1})]
            \*       /\ UNCHANGED <<matchIndex>>
            /\ matchIndex' = [matchIndex EXCEPT ![i][j] = Len(m.mlog)]
            /\ nextIndex' = nextIndex
            /\ appendEntriesResponseMsgs' = appendEntriesResponseMsgs \* \ {m}
            /\ UNCHANGED <<currentTerm, state, votedFor, votesGranted, log, commitIndex, requestVoteRequestMsgs, requestVoteResponseMsgs, appendEntriesRequestMsgs>>


\* UpdateTermRVReqAction == TRUE /\ \E m \in requestVoteRequestMsgs : UpdateTermRVReq(m.mterm, m.mdest)
\* UpdateTermRVResAction == TRUE /\ \E m \in requestVoteResponseMsgs : UpdateTermRVRes(m.mterm, m.mdest)
\* UpdateTermAEReqAction == TRUE /\ \E m \in appendEntriesRequestMsgs : UpdateTermAEReq(m.mterm, m.mdest)
\* UpdateTermAEResAction == TRUE /\ \E m \in appendEntriesResponseMsgs : UpdateTermAERes(m.mterm, m.mdest)

\* RestartAction == TRUE /\ \E i \in Server : Restart(i)
RequestVoteAction == TRUE /\ \E i \in Server : RequestVote(i)
UpdateTermAction == TRUE /\ \E m \in requestVoteRequestMsgs \cup requestVoteResponseMsgs \cup appendEntriesRequestMsgs \cup appendEntriesResponseMsgs : UpdateTerm(m, m.mterm, m.mdest)
BecomeLeaderAction == TRUE /\ \E i \in Server : BecomeLeader(i)
ClientRequestAction == TRUE /\ \E i \in Server : ClientRequest(i)
AppendEntriesAction == TRUE /\ \E i,j \in Server : AppendEntries(i, j)
HandleRequestVoteRequestAction == \E m \in requestVoteRequestMsgs : HandleRequestVoteRequest(m)
HandleRequestVoteResponseAction == \E m \in requestVoteResponseMsgs : HandleRequestVoteResponse(m)
\* RejectAppendEntriesRequestAction == \E m \in appendEntriesRequestMsgs : RejectAppendEntriesRequest(m)
AcceptAppendEntriesRequestAppendAction == \E m \in appendEntriesRequestMsgs : AcceptAppendEntriesRequestAppend(m)
\* AcceptAppendEntriesRequestTruncateAction == TRUE /\ \E m \in appendEntriesRequestMsgs : AcceptAppendEntriesRequestTruncate(m)
AcceptAppendEntriesRequestLearnCommitAction == \E m \in appendEntriesRequestMsgs : AcceptAppendEntriesRequestLearnCommit(m)
AdvanceCommitIndexAction == TRUE /\ \E i \in Server : AdvanceCommitIndex(i)
HandleAppendEntriesResponseAction == \E m \in appendEntriesResponseMsgs : HandleAppendEntriesResponse(m)

\* ElecEnabled == FALSE

ElecEnabled == 
    ENABLED (\/ HandleRequestVoteRequestAction
             \/ HandleRequestVoteResponseAction
             \/ BecomeLeaderAction)

\* Defines how the variables may transition.
Next == 
    \/ \E i \in Server : RequestVote(i)
    \/ \E m \in requestVoteRequestMsgs \cup requestVoteResponseMsgs \cup appendEntriesRequestMsgs \cup appendEntriesResponseMsgs : UpdateTerm(m, m.mterm, m.mdest)
    \/ \E m \in requestVoteRequestMsgs : HandleRequestVoteRequest(m)
    \/ \E m \in requestVoteResponseMsgs : HandleRequestVoteResponse(m)
    \/ \E i \in Server : BecomeLeader(i)
    \/ \E i \in Server : ClientRequest(i)
    \/ \E i,j \in Server : AppendEntries(i, j)
    \/ \E m \in appendEntriesRequestMsgs : AcceptAppendEntriesRequestAppend(m)
    \/ \E m \in appendEntriesResponseMsgs : HandleAppendEntriesResponse(m)
    \/ \E m \in appendEntriesRequestMsgs : AcceptAppendEntriesRequestLearnCommit(m)
    \/ \E i \in Server : AdvanceCommitIndex(i)
    \* \/ RejectAppendEntriesRequestAction
    \* \/ AcceptAppendEntriesRequestTruncateAction \* (DISABLE FOR NOW FOR SMALLER PROOF)

NextUnchanged == UNCHANGED vars

L1 == ~(\E s \in Server : Len(log[s]) > 0)
\* L1 == ~(requestVoteRequestMsgs # {})

Test1 == 
    ~(\E s,t \in Server : 
        /\ s # t
        /\ currentTerm[s] # currentTerm[t]
        /\ Len(log[s]) > 0
        /\ Len(log[t]) > 0
        /\ log[s][1] # log[t][1]
        /\ commitIndex[s] = 1
        )

CONSTANT 
    \* @type: Int;
    MaxTerm
CONSTANT 
    \* @type: Int;
    MaxLogLen
CONSTANT 
    \* @type: Int;
    MaxMsgCount

Terms == 0..MaxTerm
LogIndices == 1..MaxLogLen
LogIndicesWithZero == 0..MaxLogLen

SeqOf(S, n) == UNION {[1..m -> S] : m \in 0..n}
BoundedSeq(S, n) == SeqOf(S, n)
BoundedSeqSub(S) == BoundedSeq(S, 3)

\* In this spec we send at most 1 log entry per AppendEntries message. 
\* We encode this in the type invariant for convenience.
MaxMEntriesLen == 1

RequestVoteRequestType == [
    mtype         : {RequestVoteRequest},
    mterm         : Nat,
    \* mlastLogTerm  : Nat,
    \* mlastLogIndex : Nat,
    mlog       : Seq(Nat),
    msource       : Server,
    mdest         : Server
]

RequestVoteResponseType == [
    mtype        : {RequestVoteResponse},
    mterm        : Nat,
    mvoteGranted : BOOLEAN,
    msource      : Server,
    mdest        : Server
]

AppendEntriesRequestType == [
    mtype      : {AppendEntriesRequest},
    mterm      : Nat,
    \* mprevLogIndex  : Nat,
    \* mprevLogTerm   : Nat,
    mlog       : Seq(Nat),
    mcommitIndex   : Nat,
    msource        : Server,
    mdest          : Server
]

AppendEntriesResponseType == [
    mtype        : {AppendEntriesResponse},
    mterm        : Nat,
    \* msuccess     : BOOLEAN,
    mlog       : Seq(Nat),
    \* mmatchIndex  : Nat,
    msource      : Server,
    mdest        : Server
]

TypeOK == 
    /\ requestVoteRequestMsgs \in SUBSET RequestVoteRequestType
    /\ requestVoteResponseMsgs \in SUBSET RequestVoteResponseType
    /\ appendEntriesRequestMsgs \in SUBSET AppendEntriesRequestType
    /\ appendEntriesResponseMsgs \in SUBSET AppendEntriesResponseType
    /\ currentTerm \in [Server -> Nat]
    /\ state       \in [Server -> {Leader, Follower, Candidate}]
    /\ votedFor    \in [Server -> ({Nil} \cup Server)]
    /\ votesGranted \in [Server -> (SUBSET Server)]
    /\ nextIndex  \in [Server -> [Server -> Nat]]
    /\ matchIndex \in [Server -> [Server -> Nat]]        
    /\ log             \in [Server -> Seq(Nat)]
    /\ commitIndex     \in [Server -> Nat]
    \* Encode these basic invariants into type-correctness.
    /\ \A m \in requestVoteRequestMsgs : m.msource # m.mdest
    /\ \A m \in requestVoteResponseMsgs : m.msource # m.mdest
    /\ \A m \in appendEntriesRequestMsgs : m.msource # m.mdest
    /\ \A m \in appendEntriesResponseMsgs : m.msource # m.mdest

CurrentTermType == currentTerm \in [Server -> Nat]

\* @type: Set(Seq(Int));
\* Can be empty or contain 1 log entry.
MEntriesType == {<<>>} \cup {<<t>> : t \in Terms}

Apa_AppendEntriesRequestType == [
    mtype      : {AppendEntriesRequest},
    mterm      : Terms,
    mprevLogIndex  : LogIndicesWithZero,
    mprevLogTerm   : Terms,
    mentries       : MEntriesType,
    mcommitIndex   : LogIndicesWithZero,
    msource        : Server,
    mdest          : Server
]


Spec == Init /\ [][Next]_vars

CServerInit == {"s1", "s2", "s3"}
CServerInitSize == 3

\* CServerInit == {"s1", "s2", "s3", "s4"}
\* CServerInitSize == 4

CInit == 
    /\ Leader = "Leader"
    /\ Follower = "Follower"
    /\ Candidate = "Candidate"
    /\ Nil = "Nil"
    /\ Server = CServerInit
    /\ MaxLogLen = 3
    /\ MaxTerm = 3
    /\ RequestVoteRequest = "RequestVoteRequest"
    /\ RequestVoteResponse = "RequestVoteResponse"
    /\ AppendEntriesRequest = "AppendEntriesRequest"
    /\ AppendEntriesResponse = "AppendEntriesResponse"

\* ApaTypeOK ==
\*     \* 
\*     \* TODO: Think carefully about how to handle the bounding of these message types safely.
\*     \* 
\*     \* /\ requestVoteRequestMsgs \in SUBSET RequestVoteRequestType
\*     /\ requestVoteRequestMsgs = Gen(7)
\*     /\ \A m \in requestVoteRequestMsgs : m \in RequestVoteRequestType
\*     \* /\ requestVoteResponseMsgs \in SUBSET RequestVoteResponseType
\*     /\ requestVoteResponseMsgs = Gen(7)
\*     /\ \A m \in requestVoteResponseMsgs : m \in RequestVoteResponseType
\*     \* /\ appendEntriesResponseMsgs \in SUBSET AppendEntriesResponseType
\*     /\ appendEntriesResponseMsgs = Gen(7)
\*     /\ \A m \in appendEntriesResponseMsgs : m \in AppendEntriesResponseType
\*     \* /\ appendEntriesRequestMsgs \in SUBSET Apa_AppendEntriesRequestType
\*     /\ appendEntriesRequestMsgs = Gen(7)
\*     /\ \A m \in appendEntriesRequestMsgs : m \in Apa_AppendEntriesRequestType
\*     \* Encode these basic message invariants into type-correctness.
\*     /\ \A m \in requestVoteRequestMsgs : m.msource # m.mdest
\*     /\ \A m \in requestVoteResponseMsgs : m.msource # m.mdest
\*     /\ \A m \in appendEntriesRequestMsgs : m.msource # m.mdest
\*     /\ \A m \in appendEntriesResponseMsgs : m.msource # m.mdest
\*     /\ currentTerm \in [Server -> Terms]
\*     /\ state       \in [Server -> {Leader, Follower, Candidate}]
\*     /\ votedFor    \in [Server -> ({Nil} \cup Server)]
\*     /\ votesGranted \in [Server -> (SUBSET Server)]
\*     /\ nextIndex  \in [Server -> [Server -> LogIndicesWithZero]]
\*     /\ matchIndex \in [Server -> [Server -> LogIndicesWithZero]]    
\*     \* Constrain 'log' as a bounded sequence type.
\*     \* Note that this parameter size will, I believe, always need to be at least
\*     \* as large as the cardinality of 'Server'.
\*     /\ log = Gen(CServerInitSize)
\*     /\ \A s \in Server : \A i \in DOMAIN log[s] : log[s][i] \in Terms
\*     /\ \A s \in Server : Len(log[s]) <= MaxLogLen
\*     /\ DOMAIN log = Server
\*     /\ commitIndex     \in [Server -> LogIndicesWithZero]


----

\* INVARIANTS -------------------------

MinCommitIndex(s1, s2) ==
    IF commitIndex[s1] < commitIndex[s2]
        THEN commitIndex[s1]
        ELSE commitIndex[s2]

\* INV: LeaderHasAllAckedValues
\* A non-stale leader cannot be missing an acknowledged value
\* LeaderHasAllAckedValues ==
\*     \* for every acknowledged value
\*     \A v \in Value :
\*         IF acked[v] = TRUE
\*         THEN
\*             \* there does not exist a server that
\*             ~\E i \in Server :
\*                 \* is a leader
\*                 /\ state[i] = Leader
\*                 \* and which is the newest leader (aka not stale)
\*                 /\ ~\E l \in Server : 
\*                     /\ l # i
\*                     /\ currentTerm[l] > currentTerm[i]
\*                 \* and that is missing the value
\*                 /\ ~\E index \in DOMAIN log[i] :
\*                     log[i][index].value = v
\*         ELSE TRUE

\* INV: CommittedEntriesReachMajority
\* There cannot be a committed entry that is not at majority quorum
\* Don't use this invariant when allowing data loss on a server.
CommittedEntriesReachMajority ==
    IF \E i \in Server : state[i] = Leader /\ commitIndex[i] > 0
    THEN \E i \in Server :
           /\ state[i] = Leader
           /\ commitIndex[i] > 0
           /\ \E quorum \in SUBSET Server :
               /\ Cardinality(quorum) = (Cardinality(Server) \div 2) + 1
               /\ i \in quorum
               /\ \A j \in quorum :
                   /\ Len(log[j]) >= commitIndex[i]
                   /\ log[j][commitIndex[i]] = log[i][commitIndex[i]]
    ELSE TRUE

\* Model checking stuff.

N == 4

StateConstraint == 
    /\ \A s \in Server : currentTerm[s] <= MaxTerm
    /\ \A s \in Server : Len(log[s]) <= MaxLogLen
    \* /\ \A s, t \in Server : Cardinality({m \in requestVoteRequestMsgs : m.mdest = s /\ m.msource = t}) <= N
    \* /\ \A s, t \in Server : Cardinality({m \in requestVoteResponseMsgs : m.mdest = s /\ m.msource = t}) <= N 
    /\ Cardinality(requestVoteRequestMsgs) <= MaxMsgCount
    /\ Cardinality(requestVoteResponseMsgs) <= MaxMsgCount
    /\ Cardinality(appendEntriesRequestMsgs) <= MaxMsgCount
    /\ Cardinality(appendEntriesResponseMsgs) <= MaxMsgCount

Bait == Cardinality(requestVoteResponseMsgs) < 10



===============================================================================


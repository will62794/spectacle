--------------------------------- MODULE RaftWithReconfig --------------------------------
\* 
\* This is a formal specification for the Raft consensus algorithm with reconfiguration.
\* It allows reconfig using the protocol for single server membership changes described in Raft.
\* 

EXTENDS Naturals, FiniteSets, Sequences, TLC, Integers

\* The set of server IDs
CONSTANTS Server

\* Server states.
\* Candidate is not used, but this is fine.
CONSTANTS Follower, Candidate, Leader

\* A reserved value.
CONSTANTS Nil

----
\* Global variables

\* Servers in a given config version.
\* e.g. << {S1, S2}, {S1, S2, S3} >>
VARIABLE configs

\* The set of log entries that have been acknowledged as committed, i.e.
\* "immediately committed" entries. It does not include "prefix committed"
\* entries, which are allowed to roll back on minority nodes.
VARIABLE committedEntries

----
\* The following variables are all per server (functions with domain Server).

\* The server's term number.
VARIABLE currentTerm

\* The server's state (Follower, Candidate, or Leader).
VARIABLE state

serverVars == <<currentTerm, state>>

\* A Sequence of log entries. The index into this sequence is the index of the
\* log entry. Unfortunately, the Sequence module defines Head(s) as the entry
\* with index 1, so be careful not to use that!
VARIABLE log
logVars == <<log, committedEntries>>

\* End of per server variables.
----

\* All variables; used for stuttering (asserting state hasn't changed).
vars == <<serverVars, logVars, configs>>

----
\* Helpers

\* The term of the last entry in a log, or 0 if the log is empty.
GetTerm(xlog, index) == IF index = 0 THEN 0 ELSE xlog[index].term
LogTerm(i, index) == GetTerm(log[i], index)
LastTerm(xlog) == GetTerm(xlog, Len(xlog))

\* Return the minimum value from a set, or undefined if the set is empty.
Min(s) == CHOOSE x \in s : \A y \in s : x <= y
\* Return the maximum value from a set, or undefined if the set is empty.
Max(s) == CHOOSE x \in s : \A y \in s : x >= y

\* The config version in the node's last entry.
GetConfigVersion(i) == log[i][Len(log[i])].configVersion

\* Gets the node's first entry with a given config version.
GetConfigEntry(i, configVersion) == LET configEntries == {index \in 1..Len(log[i]) : 
                                                            log[i][index].configVersion = configVersion}
                                    IN Min(configEntries)

\* The servers that are in the same config as i.
ServerViewOn(i) == configs[GetConfigVersion(i)]

\* The set of all quorums. This just calculates simple majorities, but the only
\* important property is that every quorum overlaps with every other.
Quorum(me) == {sub \in SUBSET(ServerViewOn(me)) : Cardinality(sub) * 2 > Cardinality(ServerViewOn(me))}

----
\* Define initial values for all variables
InitServerVars == /\ currentTerm = [i \in Server |-> 0]
                  /\ state       = [i \in Server |-> Follower]
InitLogVars == /\ log              = [i \in Server |-> << [term |-> 0, configVersion |-> 1] >>]
               /\ committedEntries = {[term |-> 0, index |-> 1]}
InitConfigs == configs = << Server >>
Init == /\ InitServerVars
        /\ InitLogVars
        /\ InitConfigs

----
\* Message handlers
\* i = recipient, j = sender, m = message

AppendOplog(i, j) ==
    /\ state[i] = Follower  \* Disable primary catchup and draining
    /\ j \in ServerViewOn(i)  \* j is in the config of i.
    /\ Len(log[i]) < Len(log[j])
    /\ LastTerm(log[i]) = LogTerm(j, Len(log[i]))
    /\ log' = [log EXCEPT ![i] = Append(log[i], log[j][Len(log[i]) + 1])]
    /\ UNCHANGED <<serverVars, committedEntries, configs>>

CanRollbackOplog(i, j) ==
    /\ j \in ServerViewOn(i)  \* j is in the config of i.
    /\ Len(log[i]) > 0
    /\ \* The log with later term is more up-to-date
       LastTerm(log[i]) < LastTerm(log[j])
    /\
       \/ Len(log[i]) > Len(log[j])
       \* There seems no short-cut of OR clauses, so I have to specify the negative case
       \/ /\ Len(log[i]) <= Len(log[j])
          /\ LastTerm(log[i]) /= LogTerm(j, Len(log[i]))

RollbackOplog(i, j) ==
    /\ CanRollbackOplog(i, j)
    \* Rollback 1 oplog entry
    /\ LET new == [index2 \in 1..(Len(log[i]) - 1) |-> log[i][index2]]
         IN log' = [log EXCEPT ![i] = new]
    /\ UNCHANGED <<serverVars, committedEntries, configs>>

\* The set of nodes in my config that has log[me][logIndex] in their oplog
Agree(me, logIndex) ==
    { node \in ServerViewOn(me) :
        /\ Len(log[node]) >= logIndex
        /\ LogTerm(me, logIndex) = LogTerm(node, logIndex) }

NotBehind(me, j) == \/ LastTerm(log[me]) > LastTerm(log[j])
                    \/ /\ LastTerm(log[me]) = LastTerm(log[j])
                       /\ Len(log[me]) >= Len(log[j])

\* ACTION
\* i = the new primary node.
BecomePrimary(i, ayeVoters) ==
    /\ \A j \in ayeVoters : /\ i \in ServerViewOn(j)
                            /\ NotBehind(i, j)
                            /\ currentTerm[j] <= currentTerm[i]
    /\ ayeVoters \in Quorum(i)
    /\ state' = [index \in Server |-> IF index \notin ayeVoters
                                      THEN state[index]
                                      ELSE IF index = i THEN Leader ELSE Follower]
    /\ currentTerm' = [index \in Server |-> IF index \in (ayeVoters \union {i})
                                            THEN currentTerm[i] + 1 
                                            ELSE currentTerm[index]]
    /\ UNCHANGED <<logVars, configs>>

\* ACTION
\* Leader i receives a client request to add v to the log.
ClientWrite(i) ==
    /\ state[i] = Leader
    /\ LET entry == [term  |-> currentTerm[i], configVersion |-> GetConfigVersion(i)]
           newLog == Append(log[i], entry)
       IN  log' = [log EXCEPT ![i] = newLog]
    /\ UNCHANGED <<serverVars, committedEntries, configs>>
        
\* ACTION
\* Commit the latest log entry on a primary.
AdvanceCommitPoint(leader, ack) ==
    /\ state[leader] = Leader
    /\ ack \subseteq Agree(leader, Len(log[leader]))
    /\ ack \in Quorum(leader)
    \* If we comment out the following line, a replicated log entry from old primary will voilate the safety.
    \* [ P (2), S (), S ()]
    \* [ S (2), S (), P (3)]
    \* [ S (2), S (2), P (3)] !!! the log from term 2 shouldn't be considered as committed.
    /\ LogTerm(leader, Len(log[leader])) = currentTerm[leader]
    \* If an acknowledger has a higher term, the leader would step down.
    /\ \A j \in ack : currentTerm[j] <= currentTerm[leader]
    /\ committedEntries' = committedEntries \union {[term |-> LastTerm(log[leader]), index |-> Len(log[leader])]}
    /\ UNCHANGED <<serverVars, log, configs>>
       
UpdateTermThroughHeartbeat(i, j) ==
    /\ j \in ServerViewOn(i)  \* j is in the config of i.
    /\ currentTerm[j] > currentTerm[i]
    /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[j]]
    /\ state' = [state EXCEPT ![i] = IF ~(state[i] = Leader) THEN state[i] ELSE Follower]
    /\ UNCHANGED <<logVars, configs>>
        
Reconfig(i, newConfig) ==
    /\ state[i] = Leader
    /\ i \in newConfig
    \* Only support single node addition/removal.
    /\ Cardinality(ServerViewOn(i) \ newConfig) + Cardinality(newConfig \ ServerViewOn(i)) <= 1
    \* The config entry must be committed.
    /\ LET configEntry == GetConfigEntry(i, GetConfigVersion(i))
       IN [term |-> log[i][configEntry].term, index |-> configEntry] \in committedEntries
    \* The primary must have committed an entry in its current term.
    \* /\ \E entry \in committedEntries : entry.term = currentTerm[i] \* Condition to disable to introduce the original bug.
    /\ configs' = Append(configs, newConfig)
    /\ LET entry == [term  |-> currentTerm[i], configVersion |-> Len(configs) + 1]
           newLog == Append(log[i], entry)
       IN  log' = [log EXCEPT ![i] = newLog]
    /\ UNCHANGED <<serverVars, committedEntries>>

----
AppendOplogAction ==
    \E i,j \in Server : AppendOplog(i, j)

RollbackOplogAction ==
    \E i,j \in Server : RollbackOplog(i, j)

BecomePrimaryAction ==
    \E i \in Server : \E ayeVoters \in SUBSET(Server) : BecomePrimary(i, ayeVoters)

ClientWriteAction ==
    \E i \in Server : ClientWrite(i)
    
UpdateTermThroughHeartbeatAction ==
    \E i,j \in Server : UpdateTermThroughHeartbeat(i, j)
    
ReconfigAction ==
    \E i \in Server : \E newConfig \in SUBSET(Server) : Reconfig(i, newConfig)

----
\* Defines how the variables may transition.
Next ==
    \* --- Replication protocol
    \/ \E i,j \in Server : AppendOplog(i, j)
    \/ \E i,j \in Server : RollbackOplog(i, j)
    \/ \E i \in Server : \E ayeVoters \in SUBSET(Server) : BecomePrimary(i, ayeVoters)
    \/ \E i \in Server : ClientWrite(i)
    \/ \E leader \in Server : \E ack \in SUBSET Server : AdvanceCommitPoint(leader, ack)
    \/ \E i \in Server : \E newConfig \in SUBSET(Server) : Reconfig(i, newConfig)
    \/ \E i,j \in Server : UpdateTermThroughHeartbeat(i, j)

Liveness ==
    /\ SF_vars(AppendOplogAction)
    /\ SF_vars(RollbackOplogAction)
    \* A new primary should eventually write one entry.
    /\ WF_vars(\E i \in Server : LastTerm(log[i]) # currentTerm[i] /\ ClientWrite(i))
    \* /\ WF_vars(ClientWriteAction)

\* The specification must start with the initial state and transition according
\* to Next.
Spec == Init /\ [][Next]_vars /\ Liveness

\* RollbackCommitted and NeverRollbackCommitted are not actions.
\* They are used for verification.
RollbackCommitted(i) ==
    /\ [term |-> LastTerm(log[i]), index |-> Len(log[i])] \in committedEntries
    /\ \E j \in Server: CanRollbackOplog(i, j)

NeverRollbackCommitted ==
    \A i \in Server: ~RollbackCommitted(i)

CommittedSafety == \A x,y \in committedEntries : (x.index = y.index) => x.term = y.term
    
TwoPrimariesInSameTerm == 
    \E i, j \in Server :
        /\ i # j 
        /\ currentTerm[i] = currentTerm[j] 
        /\ state[i] = Leader 
        /\ state[j] = Leader

NoTwoPrimariesInSameTerm == ~TwoPrimariesInSameTerm

---------------------------------------------------------------

CONSTANT MaxTerm
CONSTANT MaxLogLen

StateConstraint == 
    /\ \A s \in Server : currentTerm[s] <= MaxTerm
    /\ \A s \in Server : Len(log[s]) <= MaxLogLen

Symmetry == Permutations(Server)


------------------------------------------------------------

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

\* Group element. 'children' is as a sequence of elements that will be contained in this group.
Group(children, attrs) == SVGElem("g", attrs, children, "")

Injective(f) == \A x, y \in DOMAIN f : f[x] = f[y] => x = y

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

CrownIcon == "assets/crown.svg"

CrownElem(xbase, rmid, i) == Image(xbase, i * 30, 13, 13, CrownIcon, IF state[rmid] # Leader THEN [hidden |-> "true"] ELSE <<>>)

\* Establish a fixed mapping to assign an ordering to elements in these sets.
\* ServerId == CHOOSE f \in [Server -> 1..Cardinality(Person)] : Injective(f)
SetToSeq(S) == CHOOSE f \in [1..Cardinality(S) -> S] : Injective(f)
RMId == SetToSeq(Server)

\* Animation view definition.
c1 == Circle(10, 10, 5, [fill |-> "red"])
c2 == Circle(20, 10, 5, [fill |-> "red"])
\* ServerIdDomain == 1..Cardinality(Server)
RMIdDomain == 1..Cardinality(Server)
Spacing == 40
XBase == -30
logEntryStroke(i,ind) == IF \E c \in committedEntries : c.index = ind /\ c.term = log[i][ind].term THEN "orange" ELSE "black"
logEntry(i, ybase, ind) == Group(<<Rect(18 * ind + 160, ybase, 16, 16, [fill |-> "lightgray", stroke |-> logEntryStroke(i,ind)]), 
                                   Text(18 * ind + 165, ybase + 12, ToString(log[i][ind].term), ("text-anchor" :>  "start" @@ "font-size" :> "10px"))>>, [h \in {} |-> {}])
logElem(i, ybase) == Group([ind \in DOMAIN log[i] |-> logEntry(i, ybase, ind)], [h \in {} |-> {}])
logElems ==  [i \in RMIdDomain |-> logElem(RMId[i], i * Spacing - 10)]
cs == [i \in RMIdDomain |-> 
        Group(<<Circle(XBase + 20, i * Spacing, 10, 
        [stroke |-> "black", fill |-> 
            IF state[RMId[i]] = Leader 
                THEN "gold" 
            ELSE IF state[RMId[i]] = Follower THEN "gray" 
            ELSE IF state[RMId[i]] = Follower THEN "red" ELSE "gray"]),
            CrownElem(XBase-10, RMId[i],i)>>, [h \in {} |-> {}])
        ]
\* configStr(i) ==  " (" \o ToString(configVersion[RMId[i]]) \o "," \o ToString(configTerm[RMId[i]]) \o ") " \o ToString(ServerViewOn(RMId[i]))
configStr(i) == " (" \o ToString(ServerViewOn(RMId[i])) \o "," \o ToString(GetConfigVersion(RMId[i])) \o ") "
labels == [i \in RMIdDomain |-> Text(XBase + 40, i * Spacing + 5, 
        ToString(RMId[i]) \o ", t=" \o ToString(currentTerm[RMId[i]]) \o ",  " \o configStr(i), 
        [fill |-> 
            IF state[RMId[i]] = Leader 
                THEN "black" 
            ELSE IF state[RMId[i]] = Follower THEN "black" 
            ELSE IF state[RMId[i]] = Candidate THEN "red" ELSE "gray"] @@ ("font-family" :> "monospace" @@ "font-size" :> "8px"))] 
AnimView == Group(cs \o labels \o logElems, [i \in {} |-> {}])

===============================================================================

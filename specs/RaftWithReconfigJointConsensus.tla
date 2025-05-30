--------------------------------- MODULE RaftWithReconfigJointConsensus --------------------------------
\* 
\* This is an abstract formal specification of the Raft consensus algorithm with
\* dynamic reconfiguration, using the joint consensus approach.
\* 

EXTENDS Naturals, FiniteSets, Sequences, TLC, Integers

\* The set of server IDs
CONSTANTS Server

\* Servers in a given config version.
\* e.g. << {S1, S2}, {S1, S2, S3} >>
VARIABLE configs

\* The set of log entries that have been acknowledged as committed, i.e.
\* "immediately committed" entries. It does not include "prefix committed"
\* entries, which are allowed to roll back on minority nodes.
VARIABLE committedEntries

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

\* Server states.
Leader == "Leader"
Candidate == "Candidate"
Follower == "Follower"

Nil == "Nil"

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
GetConfigVersion(i) == log[i][Len(log[i])].v

\* Gets the node's first entry with a given config version.
GetConfigEntry(i, configVersion) == LET configEntries == {index \in 1..Len(log[i]) : 
                                                            log[i][index].v = configVersion}
                                    IN Min(configEntries)

LatestConfigEntry(i) == 
        LET mind == Max({ind \in DOMAIN log[i] : "c" \in DOMAIN log[i][ind] \/ "joint" \in DOMAIN log[i][ind]}) IN
            log[i][mind]

\* The servers that are in the same config as i.
ServerViewOn(i) == configs[GetConfigVersion(i)]

\* Return a set of configs that you have to talk to. May be
\* more than one, for example, if you are in middle of joint
\* consensus reconfig.
MyConfigs(i) == 
    IF "joint" \in DOMAIN LatestConfigEntry(i) 
        THEN {LatestConfigEntry(i).cold, LatestConfigEntry(i).cnew}
    ELSE {LatestConfigEntry(i).c}

Quorums(s) == {sub \in SUBSET(s) : Cardinality(sub) * 2 > Cardinality(s)}

\* The set of all quorums. This just calculates simple majorities, but the only
\* important property is that every quorum overlaps with every other.
Quorum(me) == {sub \in SUBSET(ServerViewOn(me)) : Cardinality(sub) * 2 > Cardinality(ServerViewOn(me))}

\* The set quorum sets I have to talk to (e.g. used to support joint consensus.)
MyQuorums(me) == 
    IF "joint" \in DOMAIN LatestConfigEntry(me) 
        THEN { Quorums(LatestConfigEntry(me).cold), 
               Quorums(LatestConfigEntry(me).cnew)}
    ELSE {Quorums(LatestConfigEntry(me).c)}


\* Define initial values for all variables
Init == 
    \E c \in SUBSET Server : 
        /\ c # {}
        /\ c = Server
        /\ currentTerm = [i \in Server |-> 0]
        /\ state = [i \in Server |-> Follower]
        /\ log = [i \in Server |-> << [term |-> 0, v |-> 1, c |-> c] >>]
        /\ committedEntries = {[term |-> 0, index |-> 1]}
        /\ configs = << c >>

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
    /\ state[i] # Leader
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

AgreeInNodes(me, logIndex, nodes) ==
    { node \in nodes :
        /\ Len(log[node]) >= logIndex
        /\ LogTerm(me, logIndex) = LogTerm(node, logIndex) }


NotBehind(me, j) == \/ LastTerm(log[me]) > LastTerm(log[j])
                    \/ /\ LastTerm(log[me]) = LastTerm(log[j])
                       /\ Len(log[me]) >= Len(log[j])

\* ACTION
\* i = the new primary node.
BecomePrimary(i, ayeVoters) ==
    /\ i \in ayeVoters
    /\ \A j \in ayeVoters : /\ \A c \in MyConfigs(i) : i \in c
                            /\ NotBehind(i, j)
                            /\ currentTerm[j] <= currentTerm[i]
    /\ \A Q \in MyQuorums(i) : ayeVoters \in Q
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
    /\ LET entry == [term  |-> currentTerm[i], v |-> GetConfigVersion(i)]
           newLog == Append(log[i], entry)
       IN  log' = [log EXCEPT ![i] = newLog]
    /\ UNCHANGED <<serverVars, committedEntries, configs>>
        
\* ACTION
\* Commit the latest log entry on a primary.
AdvanceCommitPoint(leader) ==
    /\ state[leader] = Leader
    /\ \A c \in MyConfigs(leader) :
        \E ackSet \in SUBSET c : 
            /\ ackSet \subseteq AgreeInNodes(leader, Len(log[leader]), c)
            /\ ackSet \in Quorums(c)
            /\ \A j \in ackSet : currentTerm[j] = currentTerm[leader]
    /\ LogTerm(leader, Len(log[leader])) = currentTerm[leader]
    \* Has new entries to commit.
    /\ [term |-> LastTerm(log[leader]), index |-> Len(log[leader])] \notin committedEntries
    /\ committedEntries' = committedEntries \union {[term |-> log[leader][i].term, index |-> i] : i \in DOMAIN log[leader]}
    /\ UNCHANGED <<serverVars, log, configs>>
       
UpdateTerm(i, j) ==
    /\ j \in ServerViewOn(i)  \* j is in the config of i.
    /\ currentTerm[j] > currentTerm[i]
    /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[j]]
    /\ state' = [state EXCEPT ![i] = IF ~(state[i] = Leader) THEN state[i] ELSE Follower]
    /\ UNCHANGED <<logVars, configs>>

\* Reconfiguration that writes a "joint consensus" log entry i.e. phase 1 of reconfiguration
\* that writes a config with both (cold, cnew) configs.
ReconfigToJoint(i, newConfig) ==
    /\ state[i] = Leader
    /\ i \in newConfig
    \* We are not in the middle of a joint reconfiguration phase already.
    /\ "joint" \notin DOMAIN LatestConfigEntry(i)
    /\ newConfig # LatestConfigEntry(i).c
    \* The primary must have committed an entry in its current term.
    \* /\ \E entry \in committedEntries : entry.term = currentTerm[i]
    /\ configs' = Append(configs, newConfig)
    /\ LET entry == [
            term  |-> currentTerm[i], 
            v |-> Len(configs) + 1,
            cold |-> LatestConfigEntry(i).c,
            cnew |-> newConfig,
            joint |-> TRUE
        ]
           newLog == Append(log[i], entry)
       IN  log' = [log EXCEPT ![i] = newLog]
    /\ UNCHANGED <<serverVars, committedEntries>>

\* Reconfiguration that finishes an in-progress, "joint consensus" reconfig by moving us to Cnew offically.
ReconfigToNew(i, newConfig) ==
    /\ state[i] = Leader
    \* We are not in the middle of a joint reconfiguration phase already.
    /\ "joint" \in DOMAIN LatestConfigEntry(i)
    /\ newConfig = LatestConfigEntry(i).cnew
    \* Require that joint consensus entry is committed.
    /\ \E entry \in committedEntries : entry.index >= Len(log[i]) /\ entry.term = currentTerm[i]
    \* The primary must have committed an entry in its current term.
    \* /\ \E entry \in committedEntries : entry.term = currentTerm[i]
    /\ configs' = Append(configs, newConfig)
    /\ LET entry == [
            term  |-> currentTerm[i], 
            v |-> Len(configs) + 1,
            c |-> LatestConfigEntry(i).cnew
        ]
           newLog == Append(log[i], entry)
       IN  log' = [log EXCEPT ![i] = newLog]
    /\ UNCHANGED <<serverVars, committedEntries>>


\* Defines how the variables may transition.
Next ==
    \/ \E i,j \in Server : AppendOplog(i, j)
    \/ \E i,j \in Server : RollbackOplog(i, j)
    \/ \E i \in Server : \E ayeVoters \in (SUBSET(Server) \ {Server}) : BecomePrimary(i, ayeVoters)
    \/ \E i \in Server : ClientWrite(i)
    \/ \E leader \in Server : AdvanceCommitPoint(leader)
    \/ \E i \in Server : \E newConfig \in SUBSET(Server) : ReconfigToJoint(i, newConfig)
    \/ \E i \in Server : \E newConfig \in SUBSET(Server) : ReconfigToNew(i, newConfig)
    \/ \E i,j \in Server : UpdateTerm(i, j)

\* Liveness ==
    \* /\ SF_vars(AppendOplogAction)
    \* /\ SF_vars(RollbackOplogAction)
    \* A new primary should eventually write one entry.
    \* /\ WF_vars(\E i \in Server : LastTerm(log[i]) # currentTerm[i] /\ ClientWrite(i))
    \* /\ WF_vars(ClientWriteAction)

\* The specification must start with the initial state and transition according
\* to Next.
\* Spec == Init /\ [][Next]_vars /\ Liveness

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


\* 
\* Define Raft protocol state visualization.
\* 


Spacing == 40

CrownIcon == "assets/crown.svg"
BugIcon == "assets/bug.svg"

CrownElem(xbase, rmid, i) == Image(xbase, i * Spacing - 6, 13, 13, CrownIcon, IF state[rmid] # Leader THEN [hidden |-> "true"] ELSE <<>>)

\* Establish a fixed mapping to assign an ordering to elements in these sets.
\* ServerId == CHOOSE f \in [Server -> 1..Cardinality(Person)] : Injective(f)
SetToSeq(S) == CHOOSE f \in [1..Cardinality(S) -> S] : Injective(f)
RMId == SetToSeq(Server)

\* Animation view definition.
c1 == Circle(10, 10, 5, [fill |-> "red"])
c2 == Circle(20, 10, 5, [fill |-> "red"])
\* ServerIdDomain == 1..Cardinality(Server)
RMIdDomain == 1..Cardinality(Server)
XBase == -15

\* 
\* Define log elements visuals.
\* 
logEntryStyle(i,ind) == 
    IF \E c \in committedEntries : c.index = ind /\ c.term = log[i][ind].term 
        THEN ("fill" :> "lightgray" @@ "stroke" :> "limegreen" @@ "stroke-width" :> "1.5px")
        ELSE ("fill" :> "lightgray" @@ "stroke" :> "black" @@ "stroke-width" :> "1px")
logEntry(i, ybase, ind) == Group(<<Rect(18 * ind + 110, ybase, 16, 16, logEntryStyle(i,ind)), 
                                   Text(18 * ind + 115, ybase + 12, ToString(log[i][ind].term), ("text-anchor" :>  "start" @@ "font-size" :> "10px"))>>, [h \in {} |-> {}])
logElem(i, ybase) == Group([ind \in DOMAIN log[i] |-> logEntry(i, ybase, ind)], [h \in {} |-> {}])
logElems ==  [i \in RMIdDomain |-> logElem(RMId[i], i * Spacing - 9)]

\* 
\* Define server elements visuals.
\* 
cs == [i \in RMIdDomain |-> 
        Group(<<Circle(XBase + 20, i * Spacing, 10, 
        [stroke |-> "black", fill |-> 
            IF state[RMId[i]] = Leader 
                THEN "gold" 
            ELSE IF state[RMId[i]] = Follower THEN "gray" 
            ELSE IF state[RMId[i]] = Follower THEN "red" ELSE "gray"]),
            CrownElem(XBase-10, RMId[i],i)>>, [h \in {} |-> {}])
        ]

configStr(i) == ToString(ServerViewOn(RMId[i]))
labels == [i \in RMIdDomain |-> Text(XBase + 38, i * Spacing + 5, 
        \* ToString(RMId[i]) \o ", t=" \o ToString(currentTerm[RMId[i]]) \o ",  " \o configStr(i), 
        ToString(RMId[i]) \o "     " \o configStr(i), 
        [fill |-> 
            IF state[RMId[i]] = Leader 
                THEN "black" 
            ELSE IF state[RMId[i]] = Follower THEN "black" 
            ELSE IF state[RMId[i]] = Candidate THEN "red" ELSE "gray"] @@ ("font-family" :> "monospace" @@ "font-size" :> "8px"))] 

termLabels == 
    [i \in RMIdDomain |-> 
        Group(<<Text(XBase + 38 + currentTerm[RMId[i]] * 11, i * Spacing + 20, 
        "" \o ToString(currentTerm[RMId[i]]), 
            [fill |-> 
                IF state[RMId[i]] = Leader 
                    THEN "black" 
                ELSE IF state[RMId[i]] = Follower THEN "black" 
                ELSE IF state[RMId[i]] = Candidate THEN "red" ELSE "gray"] @@ ("font-family" :> "monospace" @@ "font-size" :> "7px")),
        Text(XBase + 10, i * Spacing + 20, 
        "term:", 
            [fill |-> 
                IF state[RMId[i]] = Leader 
                    THEN "black" 
                ELSE IF state[RMId[i]] = Follower THEN "black" 
                ELSE IF state[RMId[i]] = Candidate THEN "red" ELSE "gray"] @@ ("font-family" :> "monospace" @@ "font-size" :> "7px")),
        Rect(XBase + 35, i * Spacing + 20, 100, 1, [fill |-> "white"])
        >>, <<>>)]

\* 
\* Visualize committed safety violation at appropriate index.
\* 

\* Exists a different server with a conflicting committed entry at the same index.
existsConflictingEntry(ind) == \E x,y \in committedEntries : x.index = ind /\ (x.index = y.index) /\ x.term # y.term
violationEntry(ybase, ind) == Image(16 * ind + 115, ybase + 9, 13, 13, BugIcon, IF existsConflictingEntry(ind) THEN <<>> ELSE [hidden |-> "true"]) 
violationElem(ybase) == Group([ind \in 1..5 |-> violationEntry(ybase, ind)], <<>>)
safetyViolationElems ==  <<violationElem(5)>>


\* 
\* Animation view.
\* 
AnimView == Group(cs \o labels \o termLabels \o logElems \o safetyViolationElems, [i \in {} |-> {}])

===============================================================================

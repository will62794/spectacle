---- MODULE AbstractRaft_anim ----
\*
\* High level specification of Raft protocol without dynamic reconfiguration.
\*

EXTENDS Naturals, Integers, FiniteSets, Sequences, TLC


CONSTANTS Server
CONSTANTS Secondary, Primary, Nil
CONSTANT InitTerm

VARIABLE currentTerm
VARIABLE state
VARIABLE log
VARIABLE committed

vars == <<currentTerm, state, log, committed>>

\*
\* Helper operators.
\*

\* Is a sequence empty.
Empty(s) == Len(s) = 0

\* Is log entry e = <<index, term>> in the log of node 'i'.
InLog(e, i) == \E x \in DOMAIN log[i] : x = e[1] /\ log[i][x] = e[2]

\* The term of the last entry in a log, or 0 if the log is empty.
LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)]

LastEntry(xlog) == <<Len(xlog),xlog[Len(xlog)]>>

GetTerm(xlog, index) == IF index = 0 THEN 0 ELSE xlog[index]
LogTerm(i, index) == GetTerm(log[i], index)

\* The set of all quorums in a given set.
Quorums(S) == {i \in SUBSET(S) : Cardinality(i) * 2 > Cardinality(S)}

\* Is it possible for log 'i' to roll back against log 'j'. 
\* If this is true, it implies that log 'i' should remove entries from the end of its log.
CanRollback(i, j) ==
    /\ Len(log[i]) > 0
    /\ \* The log with later term is more up-to-date.
       LastTerm(log[i]) < LastTerm(log[j])
    /\ \/ Len(log[i]) > Len(log[j])
       \* There seems no short-cut of OR clauses, so we specify the negative case.
       \/ /\ Len(log[i]) <= Len(log[j])
          /\ LastTerm(log[i]) /= LogTerm(j, Len(log[i]))

\* Can node 'i' currently cast a vote for node 'j' in term 'term'.
CanVoteForOplog(i, j, term) ==
    LET logOk ==
        \/ LastTerm(log[j]) > LastTerm(log[i])
        \/ /\ LastTerm(log[j]) = LastTerm(log[i])
           /\ Len(log[j]) >= Len(log[i]) IN
    /\ currentTerm[i] < term
    /\ logOk

\* Is a log entry 'e'=<<i, t>> immediately committed in term 't' with a quorum 'Q'.
ImmediatelyCommitted(e, Q) == 
    LET eind == e[1] 
        eterm == e[2] IN
    \A s \in Q :
        /\ Len(log[s]) >= eind
        /\ InLog(e, s) \* they have the entry.
        /\ currentTerm[s] = eterm  \* they are in the same term as the log entry. 

\* Helper operator for actions that propagate the term between two nodes.
UpdateTermsExpr(i, j) ==
    /\ currentTerm[i] > currentTerm[j]
    /\ currentTerm' = [currentTerm EXCEPT ![j] = currentTerm[i]]
    /\ state' = [state EXCEPT ![j] = Secondary] 

--------------------------------------------------------------------------------

\*
\* Next state actions.
\*

\* Node 'i', a primary, handles a new client request and places the entry 
\* in its log.    
ClientRequest(i) ==
    /\ state[i] = Primary
    /\ log' = [log EXCEPT ![i] = Append(log[i], currentTerm[i])]
    /\ UNCHANGED <<currentTerm, state, committed>>

\* Node 'i' gets a new log entry from node 'j'.
GetEntries(i, j) ==
    /\ state[i] = Secondary
    \* Node j must have more entries than node i.
    /\ Len(log[j]) > Len(log[i])
       \* Ensure that the entry at the last index of node i's log must match the entry at
       \* the same index in node j's log. If the log of node i is empty, then the check
       \* trivially passes. This is the essential 'log consistency check'.
    /\ LET logOk == IF Empty(log[i])
                        THEN TRUE
                        ELSE log[j][Len(log[i])] = log[i][Len(log[i])] IN
       /\ logOk \* log consistency check
       \* If the log of node i is empty, then take the first entry from node j's log.
       \* Otherwise take the entry following the last index of node i.
       /\ LET newEntryIndex == IF Empty(log[i]) THEN 1 ELSE Len(log[i]) + 1
              newEntry      == log[j][newEntryIndex]
              newLog        == Append(log[i], newEntry) IN
              /\ log' = [log EXCEPT ![i] = newLog]
    /\ UNCHANGED <<committed, currentTerm, state>>

\*  Node 'i' rolls back against the log of node 'j'.  
RollbackEntries(i, j) ==
    /\ state[i] = Secondary
    /\ CanRollback(i, j)
    \* Roll back one log entry.
    /\ log' = [log EXCEPT ![i] = SubSeq(log[i], 1, Len(log[i])-1)]
    /\ UNCHANGED <<committed, currentTerm, state>>

\* Node 'i' gets elected as a primary.
BecomeLeader(i, voteQuorum) == 
    \* Primaries make decisions based on their current configuration.
    LET newTerm == currentTerm[i] + 1 IN
    /\ i \in voteQuorum \* The new leader should vote for itself.
    /\ \A v \in voteQuorum : CanVoteForOplog(v, i, newTerm)
    \* Update the terms of each voter.
    /\ currentTerm' = [s \in Server |-> IF s \in voteQuorum THEN newTerm ELSE currentTerm[s]]
    /\ state' = [s \in Server |->
                    IF s = i THEN Primary
                    ELSE IF s \in voteQuorum THEN Secondary \* All voters should revert to secondary state.
                    ELSE state[s]]
    /\ UNCHANGED <<log, committed>>   
            
\* Primary 'i' commits its latest log entry.
CommitEntry(i, commitQuorum) ==
    LET ind == Len(log[i]) IN
    \* Must have some entries to commit.
    /\ ind > 0
    \* This node is leader.
    /\ state[i] = Primary
    \* The entry was written by this leader.
    /\ log[i][ind] = currentTerm[i]
    \* all nodes have this log entry and are in the term of the leader.
    /\ ImmediatelyCommitted(<<ind,currentTerm[i]>>, commitQuorum)
    \* Don't mark an entry as committed more than once.
    /\ ~\E c \in committed : c[1] = ind /\ c[2] = currentTerm[i] 
    /\ committed' = committed \cup {<<ind, currentTerm[i], currentTerm[i]>>}
    /\ UNCHANGED <<currentTerm, state, log>>

\* Action that exchanges terms between two nodes and step down the primary if
\* needed. This can be safely specified as a separate action, rather than
\* occurring atomically on other replication actions that involve communication
\* between two nodes. This makes it clearer to see where term propagation is
\* strictly necessary for guaranteeing safety.
UpdateTerms(i, j) == 
    /\ UpdateTermsExpr(i, j)
    /\ UNCHANGED <<log, committed>>

Init == 
    /\ currentTerm = [i \in Server |-> InitTerm]
    /\ state       = [i \in Server |-> Secondary]
    /\ log = [i \in Server |-> <<>>]
    /\ committed = {}



Next == 
    \/ \E s \in Server : ClientRequest(s)
    \/ \E s, t \in Server : GetEntries(s, t)
    \/ \E s, t \in Server : RollbackEntries(s, t)
    \/ \E s \in Server : \E Q \in Quorums(Server) : BecomeLeader(s, Q)
    \/ \E s \in Server :  \E Q \in Quorums(Server) : CommitEntry(s, Q)
    \/ \E s,t \in Server : UpdateTerms(s, t)

Spec == Init /\ [][Next]_vars

NextUnchanged == UNCHANGED vars

--------------------------------------------------------------------------------

\*
\* Correctness properties
\*

H_OnePrimaryPerTerm == 
    \A s,t \in Server :
        (/\ state[s] = Primary 
         /\ state[t] = Primary
         /\ currentTerm[s] = currentTerm[t]) => (s = t)

LeaderAppendOnly == 
    [][\A s \in Server : state[s] = Primary => Len(log'[s]) >= Len(log[s])]_vars

\* <<index, term>> pairs uniquely identify log prefixes.
LogMatching == 
    \A s,t \in Server : 
    \A i \in DOMAIN log[s] :
        (\E j \in DOMAIN log[t] : i = j /\ log[s][i] = log[t][j]) => 
        (SubSeq(log[s],1,i) = SubSeq(log[t],1,i)) \* prefixes must be the same.

\* When a node gets elected as primary it contains all entries committed in previous terms.
LeaderCompleteness == 
    \A s \in Server : (state[s] = Primary) => 
        \A c \in committed : (c[3] < currentTerm[s] => InLog(<<c[1],c[2]>>, s))

\* \* If two entries are committed at the same index, they must be the same entry.
StateMachineSafety == 
    \A c1, c2 \in committed : (c1[1] = c2[1]) => (c1 = c2)




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

Injective(f) == \A x, y \in DOMAIN f : f[x] = f[y] => x = y

\* Establish a fixed mapping to assign an ordering to elements in these sets.
\* ServerId == CHOOSE f \in [Server -> 1..Cardinality(Person)] : Injective(f)
\* RMId == CHOOSE f \in [1..Cardinality(Server) -> Server] : Injective(f)
SetToSeq(S) == CHOOSE f \in [1..Cardinality(S) -> S] : Injective(f)
RMId == SetToSeq(Server)
\* CHOOSE f \in [1..Cardinality(Server) -> Server] : Injective(f)



\* Animation view definition.
c1 == Circle(10, 10, 5, [fill |-> "red"])
c2 == Circle(20, 10, 5, [fill |-> "red"])
\* ServerIdDomain == 1..Cardinality(Server)
RMIdDomain == 1..Cardinality(Server)
Spacing == 40
XBase == 30
logEntryStroke(i,ind) == IF \E c \in committed : c[1] = ind /\ c[2] = log[i][ind] THEN "orange" ELSE "black"
logEntry(i, ybase, ind) == Group(<<Rect(20 * ind + (XBase + 100), ybase - 5, 18, 18, [fill |-> "lightgray", stroke |-> logEntryStroke(i,ind)]), 
                                   Text(20 * ind + (XBase + 105), ybase + 8, ToString(log[i][ind]), ("text-anchor" :>  "start" @@ "font-size" :> "12px"))>>, [h \in {} |-> {}])
logElem(i, ybase) == Group([ind \in DOMAIN log[i] |-> logEntry(i, ybase, ind)], [h \in {} |-> {}])
logElems ==  [i \in RMIdDomain |-> logElem(RMId[i], i * Spacing - 5)]


CrownIcon == "https://www.svgrepo.com/download/274106/crown.svg"

CrownElem(rmid, i) == Image(20, i * Spacing - 6, 15, 15, CrownIcon, IF state[rmid] # Primary THEN [hidden |-> "true"] ELSE <<>>)

cs == [i \in RMIdDomain |-> 
        LET rmid == ToString(RMId[i]) IN
        Group(<<
            Circle(XBase + 20, i * Spacing, 10, 
            [stroke |-> "black", fill |-> 
                IF state[rmid] = Primary 
                    THEN "gold" 
                ELSE IF state[rmid] = Secondary THEN "gray" 
                ELSE IF state[rmid] = Secondary THEN "red" ELSE "gray"]), 
            CrownElem(rmid,i)>>, [a \in {} |-> {}])]
labels == [i \in RMIdDomain |-> 
        LET rmid == RMId[i] IN 
            Text(XBase + 40, i * Spacing + 5, 
            ToString(rmid) \o ", t=" \o ToString(currentTerm[rmid]), \*\o ", " \o ToString(log[rmid]), 
            [fill |-> 
            IF state[rmid] = Primary 
                THEN "black" 
            ELSE IF state[RMId[i]] = Secondary THEN "black" 
            ELSE IF state[RMId[i]] = Secondary THEN "red" ELSE "gray"])]

\* 
\* The overall animation view as one big SVG element.
\* 
AnimView == Group(cs \o labels \o logElems, [transform |-> "translate(40, 40) scale(1.25)"])



=============================================================================

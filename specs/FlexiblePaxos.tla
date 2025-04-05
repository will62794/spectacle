---- MODULE FlexiblePaxos ----

\* 
\* Source: https://github.com/fpaxos/fpaxos-tlaplus/blob/main/FPaxos.tla
\* Copyright (c) 2016: Heidi Howard
\* 

EXTENDS Integers, FiniteSets

CONSTANT
    \* @type: Set(Int);
    Value,
    \* @type: Set(Str);
    Acceptor,
    \* @type: Set(Set(Str));
    Quorum1,
    \* @type: Set(Set(Str));
    Quorum2,
    \* @type: Set(Int);
    Ballot

ASSUME QuorumAssumption ==
    /\ \A Q \in Quorum1 : Q \subseteq Acceptor
    /\ \A Q \in Quorum2 : Q \subseteq Acceptor
    /\ \A Q1 \in Quorum1 : \A Q2 \in Quorum2 : Q1 \cap Q2 # {}

VARIABLE
    \* @type: Str -> Int;
    maxBal,
    \* @type: Str -> Int;
    maxVBal,
    \* @type: Str -> Int;
    maxVal,
    \* @type: Set({bal: Int});
    1aMsgs,
    \* @type: Set({bal: Int, mbal: Int, acc: Str, mval: Int});
    1bMsgs,
    \* @type: Set({bal: Int, val: Int});
    2aMsgs,
    \* @type: Set({bal: Int, acc: Str, val: Int});
    2bMsgs

msgs == <<1aMsgs, 1bMsgs, 2aMsgs, 2bMsgs>>
vars == <<maxBal, maxVBal, maxVal, msgs>>

TypeOK ==
    /\ maxBal \in [Acceptor -> Ballot \cup {-1}]
    /\ maxVBal \in [Acceptor -> Ballot \cup {-1}]
    /\ maxVal \in [Acceptor -> Value \cup {-1}]
    /\ 1aMsgs \in SUBSET [bal : Ballot]
    /\ 1bMsgs \in SUBSET [acc : Acceptor, bal : Ballot, mbal : Ballot \cup {-1}, mval : Value \cup {-1}]
    /\ 2aMsgs \in SUBSET [bal : Ballot, val : Value]
    /\ 2bMsgs \in SUBSET [acc : Acceptor, bal : Ballot, val : Value]

Init ==
    /\ maxBal = [a \in Acceptor |-> -1]
    /\ maxVBal = [a \in Acceptor |-> -1]
    /\ maxVal = [a \in Acceptor |-> -1]
    /\ 1aMsgs = {}
    /\ 1bMsgs = {}
    /\ 2aMsgs = {}
    /\ 2bMsgs = {}

Phase1a(b) ==
    /\ 1aMsgs' = 1aMsgs \union {[bal |-> b]}
    /\ UNCHANGED <<maxBal, maxVBal, maxVal, 1bMsgs, 2aMsgs, 2bMsgs>>

Phase1b(a, b) ==
    /\ \E m \in 1aMsgs :
        /\ m.bal = b
        /\ m.bal > maxBal[a]
        /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
        /\ 1bMsgs' = 1bMsgs \union {[acc |-> a, bal |-> m.bal, mbal |-> maxVBal[a], mval |-> maxVal[a]]}
    /\ UNCHANGED <<maxVBal, maxVal, 1aMsgs, 2aMsgs, 2bMsgs>>

Phase2a(b, v, Q) ==
  /\ ~ \E m \in 2aMsgs : m.bal = b
  /\ LET Q1b == {m \in 1bMsgs : /\ m.acc \in Q
                                   /\ m.bal = b}
         Q1bv == {m \in Q1b : m.mbal \geq 0} IN
            /\ \A a \in Q : \E m \in Q1b : m.acc = a
            /\ \/ Q1bv = {}
               \/ \E m \in Q1bv :
                    /\ m.mval = v
                    /\ \A mm \in Q1bv : m.mbal \geq mm.mbal
  /\ 2aMsgs' = 2aMsgs \union {[bal |-> b, val |-> v]}
  /\ UNCHANGED <<maxBal, maxVBal, maxVal, 1aMsgs, 1bMsgs, 2bMsgs>>

Phase2b(a, b) ==
    /\ \E m \in 2aMsgs :
        /\ m.bal = b
        /\ m.bal \geq maxBal[a]
        /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
        /\ maxVBal' = [maxVBal EXCEPT ![a] = m.bal]
        /\ maxVal' = [maxVal EXCEPT ![a] = m.val]
        /\ 2bMsgs' = 2bMsgs \union {[acc |-> a, bal |-> m.bal, val |-> m.val]}
    /\ UNCHANGED <<1aMsgs, 1bMsgs, 2aMsgs>>

Next ==
    \/ \E b \in Ballot : Phase1a(b)
    \/ \E b \in Ballot : \E v \in Value : \E Q \in Quorum1 : Phase2a(b, v, Q)
    \/ \E a \in Acceptor : \E b \in Ballot : Phase1b(a, b)
    \/ \E a \in Acceptor, b \in Ballot : Phase2b(a, b)

Spec == Init /\ [][Next]_vars

\* MCAcceptor == {"a1", "a2", "a3"}
\* MCValue    == 0..2
\* MCQuorum1 == {{"a1", "a2"}, {"a1", "a3"}, {"a2", "a3"}}
\* MCQuorum2 == {{"a1", "a2"}, {"a1", "a3"}, {"a2", "a3"}}
\* MCBallot == 0..2

Sent2b(a,v,b) ==
    \E m \in 2bMsgs:
        /\ m.acc = a
        /\ m.val = v
        /\ m.bal = b

Sent2a(v,b) ==
    \E m \in 2aMsgs:
        /\ m.val = v
        /\ m.bal = b

Agreed(v,b) ==
    \E Q \in Quorum2:
        \A a \in Q: Sent2b(a,v,b)

Decided(v) ==
    \A b \in Ballot: Agreed(v,b)

NoFutureProposal(v,b) ==
    \A v2 \in Value:
        \A b2 \in Ballot: (b2 > b /\ Sent2a(v2,b2)) => v=v2

SafeValue ==
    \A v \in Value:
        \A b \in Ballot: Agreed(v,b) => NoFutureProposal(v,b)

Safety == Cardinality({ v \in Value: Decided(v) }) \leq 1

\* Below is my first attempt at a inductive invariant. Not currently working

OneValueAgreedPerBallot ==
    \A b \in Ballot: Cardinality({ v \in Value: Agreed(v,b) }) \leq 1

OneVotePerAcceptorPerBallot ==
    \A a \in Acceptor:
        \A b \in Ballot: Cardinality({ v \in Value: Sent2b(a,v,b) }) \leq 1

SafeStates ==
    \A a \in Acceptor:
        /\ \/ maxBal[a] = -1
           \/ \E m \in 1aMsgs: m.bal = maxBal[a]
           \/ \E m \in 2aMsgs: m.bal = maxBal[a]
        /\ maxBal[a] >= maxVBal[a]
        /\ \A m \in 1bMsgs:
            /\ m.acc = a
            => /\ m.bal <= maxBal[a]
               /\ m.mbal <= maxVBal[a]
        /\ \A m \in 2bMsgs:
            /\ m.acc = a
            => /\ m.bal <= maxBal[a]
               /\ m.bal <= maxVBal[a]
        /\ \/ (maxVBal[a] = -1 /\ maxVal[a] = -1)
           \/ \E m \in 2aMsgs:
                /\ m.bal = maxVBal[a]
                /\ m.val = maxVal[a]


Safe1b ==
    \A m \in 1bMsgs:
            /\ \E a \in Acceptor:
                /\ m.acc = a
                /\ \/ /\ m.mbal = -1
                      /\ m.mval = -1
                      \* acceptor $a$ never accepted a proposal in a smaller ballot
                      /\ ~ \E m2 \in 2bMsgs:
                        /\ m2.acc = a
                        /\ m2.bal < m.bal
                      /\ \A m2 \in 1bMsgs:
                        /\ m2.acc = a
                        /\ m2.bal < m.bal
                        => m2.mbal = -1 /\ m2.mval = -1
                   \/ \E m2 \in 2aMsgs:
                        /\ m.mbal = m2.bal
                        /\ m.mval = m2.val
            /\ m.bal > m.mbal
            /\ \A m2 \in 1bMsgs:
                /\ m2.mbal = m.mbal
                => m2.mval = m.mval

Safe2a ==
    \A m \in 2aMsgs:
        /\ \E Q \in Quorum1:
            \E a_max \in Q:
                \E bal_max \in Ballot \cup {-1}:
                    /\ \E m_max \in 1bMsgs:
                        /\ m_max.acc = a_max
                        /\ m_max.bal = m.bal
                        /\ m_max.mbal = bal_max
                        /\ \/ bal_max = -1
                            \/ m_max.mval = m.val
                    /\ \A a2 \in Q:
                        \E m2 \in 1bMsgs:
                            /\ m2.acc = a2
                            /\ m2.bal = m.bal
                            /\ bal_max \geq m2.mbal
        /\ \A m2 \in 2aMsgs:
            /\ m2.bal = m.bal
            => m2.val = m.val

Safe2b ==
    \A m \in 2bMsgs:
        /\ \E a \in Acceptor:
            /\ m.acc = a
            /\ \/ /\ maxBal[a] \geq m.bal
                  /\ maxVBal[a] = m.bal
                  /\ maxVal[a] = m.val
               \/ m.bal < maxBal[a]
        /\ \E m2 \in 2aMsgs:
            /\ m2.bal = m.bal
            /\ m2.val = m.val


Inv ==
    /\ TypeOK
    /\ SafeStates
    /\ Safe1b
    /\ Safe2a
    /\ Safe2b
    /\ SafeValue
    /\ Safety

====
---- MODULE gfd ----
EXTENDS TLC, Naturals

\* 
\* Abstract model of Git for Data:
\* Based on original source at https://github.com/BauplanLabs/git_for_data/blob/main/src/blog_series/part1/alloy/gsd.als.
\* 

CONSTANT TableId

\* An abstract identifier that represents a snapshot/version of a specific table.
CONSTANT Snapshot

\* Commits are pointers to state of the data system at a point in time.
\* Include some type of unique identifier for each commit?
VARIABLE commits

\* Branches are simply movable pointers to commits (via referencing their commitId).
VARIABLE branches

\* Assume we can label commits with globally unique identifiers, analogous to git commit hashes.
\* We don't actually derive the commit identifier based on hash of the parent state as in actual Git,
\* but it serves essentially the same purpose i.e. a globally unique identifier for some commit/node in the
\* global commit DAG.
VARIABLE nextCommitId

EmptyFn == [x \in {} |-> {}]

GetCommit(cid) == CHOOSE x \in {cm \in commits : cm.commitId = cid} : TRUE

\* Create a new table 't' on branch 'b'.
CreateTable(b, t, s) == 
    /\ t \notin DOMAIN(GetCommit(b).tables)
    /\ commits' = commits \cup {[commitId |-> nextCommitId, parents |-> {b}, tables |-> GetCommit(b).tables @@ (t :> s)]}
    /\ nextCommitId' = nextCommitId + 1
    /\ branches' = (branches \cap {b}) \cup {nextCommitId}
    
\* Models a generic transformation on branch 'b' that creates a new snapshot 's'
\* for table 't'. A new table is created if 't' was not already mapped to some snapshot.
CreateSnapshot(b, t, s) == 
    /\ commits' = commits \cup {[commitId |-> nextCommitId, parents |-> {b}, tables |-> GetCommit(b).tables @@ (t :> s)]}
    /\ nextCommitId' = nextCommitId + 1
    /\ branches' = (branches \cap {b}) \cup {nextCommitId}

\* Incorporates changes in commit 'c' into branch 'b'.
Merge(b, c) == 
    /\ branches' = (branches \cap {b}) \cup {c}

\* Fast-forward merge of branch 'b' into branch 'c'.
FFMerge == TRUE

\* Smart merge of branch 'b' into branch 'c'.
SmartMerge == TRUE

Init == 
    /\ commits = {[commitId |-> 0, parents |-> {}, tables |-> EmptyFn]}
    /\ branches = {0}
    /\ nextCommitId = 1

Next ==
    \/ \E b \in branches, t \in TableId, s \in Snapshot : CreateTable(b, t, s)
    \/ \E b \in branches, t \in TableId, s \in Snapshot : CreateSnapshot(b, t, s)


====
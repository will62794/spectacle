---- MODULE gfd ----
EXTENDS TLC, Naturals, FiniteSets, Sequences

\* 
\* Abstract model of Git for Data:
\* Based on original source at https://github.com/BauplanLabs/git_for_data/blob/main/src/blog_series/part1/alloy/gsd.als.
\* 

CONSTANT TableId

\* An abstract identifier that represents a snapshot/version of a specific table.
CONSTANT Snapshot

\* Assume there is a fixed, max number of unique branch identifiers, each of
\* which may or may not be used to currently point to a commit.
CONSTANT BranchId

\* Commits are pointers to state of the data system at a point in time.
\* Include some type of unique identifier for each commit?
VARIABLE commits

\* Branches are simply movable pointers to commits (via referencing their commitId).
\* We represent them as a map from branch identifiers -> commits, where the commit
\* can possible be empty if such a branch doesn't exist yet.
VARIABLE branches

\* Assume we can label commits with globally unique identifiers, analogous to git commit hashes.
\* We don't actually derive the commit identifier based on hash of the parent state as in actual Git,
\* but it serves essentially the same purpose i.e. a globally unique identifier for some commit/node in the
\* global commit DAG.
VARIABLE nextCommitId

EmptyFn == [x \in {} |-> {}]

CommitIds == {c.commitId : c \in commits}

GetCommit(cid) == CHOOSE x \in {cm \in commits : cm.commitId = cid} : TRUE

\* Create a new table 't' on branch 'b'.
CreateTable(b, t, s) == 
    /\ b \in DOMAIN branches
    /\ t \notin DOMAIN(GetCommit(branches[b]).tables)
    /\ commits' = commits \cup {[commitId |-> nextCommitId, parents |-> {branches[b]}, tables |-> GetCommit(branches[b]).tables @@ (t :> s)]}
    /\ nextCommitId' = nextCommitId + 1
    /\ branches' = [branches EXCEPT ![b] = nextCommitId]
    
\* Models a generic transformation on branch 'b' that creates a new snapshot 's'
\* for table 't'. A new table is created if 't' was not already mapped to some snapshot.
CreateSnapshot(b, t, s) == 
    /\ b \in DOMAIN branches
    /\ commits' = commits \cup {[commitId |-> nextCommitId, parents |-> {branches[b]}, tables |-> GetCommit(branches[b]).tables @@ (t :> s)]}
    /\ nextCommitId' = nextCommitId + 1
    /\ branches' = [branches EXCEPT ![b] = nextCommitId]

\* Creates a new branch starting at commit 'c'.
CreateBranch(c, b) == 
    /\ b \notin DOMAIN branches
    /\ branches' = branches @@ (b :> c)
    /\ UNCHANGED <<commits, nextCommitId>>

\* Merge commit 'c' into branch 'b'.
Merge(b, c) == 
    /\ branches' = (branches \ {b}) \cup {c}

SeqOf(set, n) == UNION {[1..m -> set] : m \in 0..n}

SimplePath(V, E) ==
    \* A simple path is a path with no repeated nodes.
    {p \in SeqOf(V, Cardinality(V)) :
             /\ p # << >>
             /\ Cardinality({ p[i] : i \in DOMAIN p }) = Len(p)
             /\ \A i \in 1..(Len(p)-1) : <<p[i], p[i+1]>> \in E}

SimplePathsFrom(V, E, start, target) ==
    {p \in SimplePath(V, E) : p[1] = start /\ p[Len(p)] = target}


ParentEdges == UNION {{<<c.commitId, p>> : p \in c.parents} : c \in commits}

\* Is commit 'ctarget' backwards reachable from commit 'cstart' via parent pointers?
BackwardsReachable(cstart, ctarget) ==
    SimplePathsFrom(CommitIds, ParentEdges, cstart, ctarget) # {}

\* The most recent common ancestor between two commits 'c1' and 'c2'.
NewestCommonAncestor(ci, cj) == TRUE

RECURSIVE IsAncestor(_, _)

\* Is commit 'ci' an ancestor of commit 'cj'?
IsAncestor(ci, cj) == 
    \/ ci \in GetCommit(cj).parents
    \/ \E c \in GetCommit(cj).parents : IsAncestor(ci, c)


\* 
\* Fast-forward merge of commit 'c' into branch 'b'.
\* 
\* A fast-forward merge only needs to update the commit that branch 'b' points
\* to. We consider this as possible when 'c' can be reached by following a
\* linear sequence of commits i.e. when the commit of branch 'b' is backwards reachable from commit 'c'.
\* 
FFMerge(c, b) == 
    /\ b \in DOMAIN branches
    /\ branches[b] # c
    \* Is the commit directly reachable from 'b' via parent pointers?
    /\ IsAncestor(c, branches[b])
    /\ branches' = [branches EXCEPT ![b] = c]
    /\ UNCHANGED <<commits, nextCommitId>>

\*  A merge of diverging commits. This is only possible if the sets of tables
\*  that were modified since `b` and `c` diverged from their most recent common
\*  ancestor are disjoint.
SmartMerge(b, c) == 
    /\ ~IsAncestor(b, c)
    /\ ~IsAncestor(c, b)
    

Init == 
    /\ commits = {[commitId |-> 0, parents |-> {}, tables |-> EmptyFn]}
    /\ \E b \in BranchId : branches = (b :> 0)
    /\ nextCommitId = 1

Next ==
    \/ \E b \in BranchId, t \in TableId, s \in Snapshot : CreateTable(b, t, s)
    \/ \E b \in BranchId, t \in TableId, s \in Snapshot : CreateSnapshot(b, t, s)
    \/ \E c \in CommitIds, b \in BranchId : CreateBranch(c, b)
    \/ \E c \in CommitIds, b \in BranchId : FFMerge(c, b)


====
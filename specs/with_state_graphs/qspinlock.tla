---------------------------- MODULE qspinlock --------------------------------
\*
\* Linux queued spinlocks model (modified to avoid the cmpxchg loops)
\*
\* Original source: https://web.git.kernel.org/pub/scm/linux/kernel/git/cmarinas/kernel-tla.git/tree/qspinlock.tla
\* 
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS CPUS,
	  MAX_NODES,
	  PENDING_LOOPS

ASSUME MAX_NODES \in Nat \ {0}

\* NoCPU	== CHOOSE cpu : cpu \notin CPUS
NoCPU	== "NoCPU"
THREADS	== CPUS \X (1..MAX_NODES)

(* --algorithm qspinlock {
variables
	\* One qspinlock per node (a.k.a. priority level)
	qspinlock	= [l \in 1..MAX_NODES |-> LockVal(FALSE, FALSE, 0, NoCPU)];
	\* One mcs_lock per thread
	mcs_lock	= [t \in THREADS |->
				[next	|-> NODE_ZERO,
				 locked	|-> FALSE,
				 count	|-> 0]];

	\* priority level
	priority	= [p \in CPUS |-> 1];

	ret_trylock	= [p \in THREADS |-> FALSE];

define {
	ProcessEnabled(self) == self[2] >= priority[self[1]]

	LockVal(l, p, i, c) == [locked		|-> l,
				pending		|-> p,
				tail_idx	|-> i,
				tail_cpu	|-> c]
	ZERO_VAL	== LockVal(FALSE, FALSE, 0, NoCPU)
	LOCKED_VAL	== LockVal(TRUE, FALSE, 0, NoCPU)
	PENDING_VAL	== LockVal(FALSE, TRUE, 0, NoCPU)
	NEG_LOCKED_MASK(val) == val.pending \/ val.tail_idx # 0 \/ val.tail_cpu # NoCPU
	TAIL_MASK(val)	== val.tail_idx # 0 \/ val.tail_cpu # NoCPU

	NODE_ZERO	== << NoCPU, 0 >>

	\* lock addresses
	Lock(self)	== self[2]
	McsNode(p, i)	== << p, i >>

	QLockType	== [locked:	BOOLEAN,
			    pending:	BOOLEAN,
			    tail_idx:	Nat,
			    tail_cpu:	CPUS \cup {NoCPU}]
	McsLockType	== [next:	THREADS \cup {NODE_ZERO},
			    locked:	BOOLEAN,
			    count:	Nat]
	TypeInv	== /\ mcs_lock \in [THREADS -> McsLockType]
		   /\ qspinlock \in [1..MAX_NODES -> QLockType]

	ExclInv	== \A t1, t2 \in THREADS : t1[1] # t2[1] /\ t1[2] = t2[2] =>
			~((pc[t1] = "cs") /\ (pc[t2] = "cs"))

	LockAny	== \E t \in THREADS : pc[t] = "sl1" ~> pc[t] = "cs"
	LockAll	== \A p \in CPUS : \E n \in 1..MAX_NODES :
			pc[<< p, n >>] = "sl1" ~> pc[<< p, n >>] = "cs"

	\* Symmetry optimisations
	Perms	== Permutations(CPUS)
}

macro priority_enter(level) {
	level := priority[self[1]];
	priority[self[1]] := self[2];
}

macro priority_exit(level) {
	priority[self[1]] := level;
}

\* atomic cmpxchg
macro cmpxchg(v, o, n, ret) {
	ret := v;
	if (v = o)
		v := n;
}

procedure spin_lock(lock)
	variable val;
{
sl1:	cmpxchg(qspinlock[lock], ZERO_VAL, LOCKED_VAL, val);
sl2:	if (val = ZERO_VAL)
		return;
sl3:	call spin_lock_slowpath(lock, val);
	return;
}

procedure spin_unlock(lock)
{
su1:	qspinlock[lock].locked := FALSE;
	return;
}

procedure spin_trylock(lock)
{
stl1:	if (qspinlock[lock] = ZERO_VAL) {
		qspinlock[lock] := LOCKED_VAL;
		ret_trylock[self] := TRUE;
	} else {
		ret_trylock[self] := FALSE;
	};
	return;
}

procedure spin_lock_slowpath(lock, val)
	variables old, next, prev, node, idx, cnt = PENDING_LOOPS;
{
sp1:	\* wait for in-progress pending->locked hand-overs (bounded)
	if (val = PENDING_VAL) {
sp1_1:		while (qspinlock[lock] = PENDING_VAL /\ cnt # 0)
			cnt := cnt - 1;
		val := qspinlock[lock];
	};

sp1_2:	\* if we observe any contention, queue
	if (NEG_LOCKED_MASK(val))
		goto queue;

sp2:	\* trylock \/ pending
	\* atomic_fetch_or
	val := qspinlock[lock];
	qspinlock[lock].pending := TRUE;
sp3:	if (~NEG_LOCKED_MASK(val)) {
		\* we're pending, wait for the owner to go away
		\* smp_cond_load_acquire(!(VAL & LOCKED_MASK))
		if (val.locked)
			await ~qspinlock[lock].locked;

		\* take ownership and clear pending
		\* clear_pending_set_locked
		qspinlock[lock].pending := FALSE || qspinlock[lock].locked := TRUE;

		return;
	};

	\* if pending was clear but there are waiters, undo the setting of
	\* pending before queuing
sp4:	if (~val.pending)
		qspinlock[lock].pending := FALSE;

queue:
	node := McsNode(self[1], 1);
	idx := mcs_lock[node].count + 1;
	mcs_lock[node].count := mcs_lock[node].count + 1;

sp11:	node := McsNode(self[1], idx);
	mcs_lock[node].locked := FALSE || mcs_lock[node].next := NODE_ZERO;

	call spin_trylock(lock);
sp13:	if (ret_trylock[self])
		goto release;

sp14:	\* xchg_tail
	old := LockVal(FALSE, FALSE, qspinlock[lock].tail_idx, qspinlock[lock].tail_cpu);
	qspinlock[lock].tail_idx := idx || qspinlock[lock].tail_cpu := self[1];
	next := NODE_ZERO;

sp15:	if (TAIL_MASK(old)) {
		prev := McsNode(old.tail_cpu, old.tail_idx);
		mcs_lock[prev].next := node;

sp16:		\* mcs_spin_lock_contended
		await mcs_lock[node].locked;

		next := mcs_lock[node].next;
	};

sp18:	\* smp_cond_load_acquire(!(VAL & LOCKED_PENDING_MASK))
	await ~qspinlock[lock].locked /\ ~qspinlock[lock].pending;
	val := qspinlock[lock];

locked:	\* claim the lock
	if (val.tail_idx = idx /\ val.tail_cpu = self[1]) {
		cmpxchg(qspinlock[lock], val, LOCKED_VAL, old);
		if (old = val)
			goto release;	\* no contention
	};

	\* either somebody is queued behind us or pending is set
sp21:	qspinlock[lock].locked := TRUE;

	\* contended path; wait for next if not observed yet, release
	if (next = NODE_ZERO) {
		await mcs_lock[node].next # NODE_ZERO;
		next := mcs_lock[node].next;
	};

	\* mcs_spin_unlock_contended
	mcs_lock[next].locked := TRUE;

release:
	mcs_lock[McsNode(self[1], 1)].count := mcs_lock[McsNode(self[1], 1)].count - 1;
	return;
}

fair process (thread \in THREADS)
	variable priority_level;
{
t1:	while (TRUE) {
		priority_enter(priority_level);
		call spin_lock(Lock(self));
cs:		skip;
		call spin_unlock(Lock(self));
t2:		priority_exit(priority_level);
	}
}
} *)
\* BEGIN TRANSLATION
\* Procedure variable val of procedure spin_lock at line 91 col 18 changed to val_
\* Parameter lock of procedure spin_lock at line 90 col 21 changed to lock_
\* Parameter lock of procedure spin_unlock at line 100 col 23 changed to lock_s
\* Parameter lock of procedure spin_trylock at line 106 col 24 changed to lock_sp
CONSTANT defaultInitValue
VARIABLES pc, qspinlock, mcs_lock, priority, ret_trylock, stack

(* define statement *)
ProcessEnabled(self) == self[2] >= priority[self[1]]

LockVal(l, p, i, c) == [locked          |-> l,
                        pending         |-> p,
                        tail_idx        |-> i,
                        tail_cpu        |-> c]
ZERO_VAL        == LockVal(FALSE, FALSE, 0, NoCPU)
LOCKED_VAL      == LockVal(TRUE, FALSE, 0, NoCPU)
PENDING_VAL     == LockVal(FALSE, TRUE, 0, NoCPU)
NEG_LOCKED_MASK(val) == val.pending \/ val.tail_idx # 0 \/ val.tail_cpu # NoCPU
TAIL_MASK(val)  == val.tail_idx # 0 \/ val.tail_cpu # NoCPU

NODE_ZERO       == << NoCPU, 0 >>


Lock(self)      == self[2]
McsNode(p, i)   == << p, i >>

QLockType       == [locked:     BOOLEAN,
                    pending:    BOOLEAN,
                    tail_idx:   Nat,
                    tail_cpu:   CPUS \cup {NoCPU}]
McsLockType     == [next:       THREADS \cup {NODE_ZERO},
                    locked:     BOOLEAN,
                    count:      Nat]
TypeInv == /\ mcs_lock \in [THREADS -> McsLockType]
           /\ qspinlock \in [1..MAX_NODES -> QLockType]

ExclInv == \A t1, t2 \in THREADS : t1[1] # t2[1] /\ t1[2] = t2[2] =>
                ~((pc[t1] = "cs") /\ (pc[t2] = "cs"))

LockAny == \E t \in THREADS : pc[t] = "sl1" ~> pc[t] = "cs"
LockAll == \A p \in CPUS : \E n \in 1..MAX_NODES :
                pc[<< p, n >>] = "sl1" ~> pc[<< p, n >>] = "cs"


Perms   == Permutations(CPUS)

VARIABLES lock_, val_, lock_s, lock_sp, lock, val, old, next, prev, node, idx, 
          cnt, priority_level

vars == << pc, qspinlock, mcs_lock, priority, ret_trylock, stack, lock_, val_, 
           lock_s, lock_sp, lock, val, old, next, prev, node, idx, cnt, 
           priority_level >>

ProcSet == (THREADS)

Init == (* Global variables *)
        /\ qspinlock = [l \in 1..MAX_NODES |-> LockVal(FALSE, FALSE, 0, NoCPU)]
        /\ mcs_lock = [t \in THREADS |->
                            [next   |-> NODE_ZERO,
                             locked |-> FALSE,
                             count  |-> 0]]
        /\ priority = [p \in CPUS |-> 1]
        /\ ret_trylock = [p \in THREADS |-> FALSE]
        (* Procedure spin_lock *)
        /\ lock_ = [ self \in ProcSet |-> defaultInitValue]
        /\ val_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure spin_unlock *)
        /\ lock_s = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure spin_trylock *)
        /\ lock_sp = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure spin_lock_slowpath *)
        /\ lock = [ self \in ProcSet |-> defaultInitValue]
        /\ val = [ self \in ProcSet |-> defaultInitValue]
        /\ old = [ self \in ProcSet |-> defaultInitValue]
        /\ next = [ self \in ProcSet |-> defaultInitValue]
        /\ prev = [ self \in ProcSet |-> defaultInitValue]
        /\ node = [ self \in ProcSet |-> defaultInitValue]
        /\ idx = [ self \in ProcSet |-> defaultInitValue]
        /\ cnt = [ self \in ProcSet |-> PENDING_LOOPS]
        (* Process thread *)
        /\ priority_level = [self \in THREADS |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "t1"]

sl1(self) == /\ pc[self] = "sl1"
             /\ val_' = [val_ EXCEPT ![self] = qspinlock[lock_[self]]]
             /\ IF (qspinlock[lock_[self]]) = ZERO_VAL
                   THEN /\ qspinlock' = [qspinlock EXCEPT ![lock_[self]] = LOCKED_VAL]
                   ELSE /\ TRUE
                        /\ UNCHANGED qspinlock
             /\ pc' = [pc EXCEPT ![self] = "sl2"]
             /\ UNCHANGED << mcs_lock, priority, ret_trylock, stack, lock_, 
                             lock_s, lock_sp, lock, val, old, next, prev, node, 
                             idx, cnt, priority_level >>

sl2(self) == /\ pc[self] = "sl2"
             /\ IF val_[self] = ZERO_VAL
                   THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                        /\ val_' = [val_ EXCEPT ![self] = Head(stack[self]).val_]
                        /\ lock_' = [lock_ EXCEPT ![self] = Head(stack[self]).lock_]
                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "sl3"]
                        /\ UNCHANGED << stack, lock_, val_ >>
             /\ UNCHANGED << qspinlock, mcs_lock, priority, ret_trylock, 
                             lock_s, lock_sp, lock, val, old, next, prev, node, 
                             idx, cnt, priority_level >>

sl3(self) == /\ pc[self] = "sl3"
             /\ /\ lock' = [lock EXCEPT ![self] = lock_[self]]
                /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "spin_lock_slowpath",
                                                         pc        |->  Head(stack[self]).pc,
                                                         old       |->  old[self],
                                                         next      |->  next[self],
                                                         prev      |->  prev[self],
                                                         node      |->  node[self],
                                                         idx       |->  idx[self],
                                                         cnt       |->  cnt[self],
                                                         lock      |->  lock[self],
                                                         val       |->  val[self] ] >>
                                                     \o Tail(stack[self])]
                /\ val' = [val EXCEPT ![self] = val_[self]]
                /\ val_' = [val_ EXCEPT ![self] = Head(stack[self]).val_]
             /\ old' = [old EXCEPT ![self] = defaultInitValue]
             /\ next' = [next EXCEPT ![self] = defaultInitValue]
             /\ prev' = [prev EXCEPT ![self] = defaultInitValue]
             /\ node' = [node EXCEPT ![self] = defaultInitValue]
             /\ idx' = [idx EXCEPT ![self] = defaultInitValue]
             /\ cnt' = [cnt EXCEPT ![self] = PENDING_LOOPS]
             /\ pc' = [pc EXCEPT ![self] = "sp1"]
             /\ UNCHANGED << qspinlock, mcs_lock, priority, ret_trylock, lock_, 
                             lock_s, lock_sp, priority_level >>

spin_lock(self) == sl1(self) \/ sl2(self) \/ sl3(self)

su1(self) == /\ pc[self] = "su1"
             /\ qspinlock' = [qspinlock EXCEPT ![lock_s[self]].locked = FALSE]
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ lock_s' = [lock_s EXCEPT ![self] = Head(stack[self]).lock_s]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << mcs_lock, priority, ret_trylock, lock_, val_, 
                             lock_sp, lock, val, old, next, prev, node, idx, 
                             cnt, priority_level >>

spin_unlock(self) == su1(self)

stl1(self) == /\ pc[self] = "stl1"
              /\ IF qspinlock[lock_sp[self]] = ZERO_VAL
                    THEN /\ qspinlock' = [qspinlock EXCEPT ![lock_sp[self]] = LOCKED_VAL]
                         /\ ret_trylock' = [ret_trylock EXCEPT ![self] = TRUE]
                    ELSE /\ ret_trylock' = [ret_trylock EXCEPT ![self] = FALSE]
                         /\ UNCHANGED qspinlock
              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
              /\ lock_sp' = [lock_sp EXCEPT ![self] = Head(stack[self]).lock_sp]
              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED << mcs_lock, priority, lock_, val_, lock_s, lock, 
                              val, old, next, prev, node, idx, cnt, 
                              priority_level >>

spin_trylock(self) == stl1(self)

sp1(self) == /\ pc[self] = "sp1"
             /\ IF val[self] = PENDING_VAL
                   THEN /\ pc' = [pc EXCEPT ![self] = "sp1_1"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "sp1_2"]
             /\ UNCHANGED << qspinlock, mcs_lock, priority, ret_trylock, stack, 
                             lock_, val_, lock_s, lock_sp, lock, val, old, 
                             next, prev, node, idx, cnt, priority_level >>

sp1_1(self) == /\ pc[self] = "sp1_1"
               /\ IF qspinlock[lock[self]] = PENDING_VAL /\ cnt[self] # 0
                     THEN /\ cnt' = [cnt EXCEPT ![self] = cnt[self] - 1]
                          /\ pc' = [pc EXCEPT ![self] = "sp1_1"]
                          /\ val' = val
                     ELSE /\ val' = [val EXCEPT ![self] = qspinlock[lock[self]]]
                          /\ pc' = [pc EXCEPT ![self] = "sp1_2"]
                          /\ cnt' = cnt
               /\ UNCHANGED << qspinlock, mcs_lock, priority, ret_trylock, 
                               stack, lock_, val_, lock_s, lock_sp, lock, old, 
                               next, prev, node, idx, priority_level >>

sp1_2(self) == /\ pc[self] = "sp1_2"
               /\ IF NEG_LOCKED_MASK(val[self])
                     THEN /\ pc' = [pc EXCEPT ![self] = "queue"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "sp2"]
               /\ UNCHANGED << qspinlock, mcs_lock, priority, ret_trylock, 
                               stack, lock_, val_, lock_s, lock_sp, lock, val, 
                               old, next, prev, node, idx, cnt, priority_level >>

sp2(self) == /\ pc[self] = "sp2"
             /\ val' = [val EXCEPT ![self] = qspinlock[lock[self]]]
             /\ qspinlock' = [qspinlock EXCEPT ![lock[self]].pending = TRUE]
             /\ pc' = [pc EXCEPT ![self] = "sp3"]
             /\ UNCHANGED << mcs_lock, priority, ret_trylock, stack, lock_, 
                             val_, lock_s, lock_sp, lock, old, next, prev, 
                             node, idx, cnt, priority_level >>

sp3(self) == /\ pc[self] = "sp3"
             /\ IF ~NEG_LOCKED_MASK(val[self])
                   THEN /\ IF val[self].locked
                              THEN /\ ~qspinlock[lock[self]].locked
                              ELSE /\ TRUE
                        /\ qspinlock' = [qspinlock EXCEPT ![lock[self]].pending = FALSE,
                                                          ![lock[self]].locked = TRUE]
                        /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                        /\ old' = [old EXCEPT ![self] = Head(stack[self]).old]
                        /\ next' = [next EXCEPT ![self] = Head(stack[self]).next]
                        /\ prev' = [prev EXCEPT ![self] = Head(stack[self]).prev]
                        /\ node' = [node EXCEPT ![self] = Head(stack[self]).node]
                        /\ idx' = [idx EXCEPT ![self] = Head(stack[self]).idx]
                        /\ cnt' = [cnt EXCEPT ![self] = Head(stack[self]).cnt]
                        /\ lock' = [lock EXCEPT ![self] = Head(stack[self]).lock]
                        /\ val' = [val EXCEPT ![self] = Head(stack[self]).val]
                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "sp4"]
                        /\ UNCHANGED << qspinlock, stack, lock, val, old, next, 
                                        prev, node, idx, cnt >>
             /\ UNCHANGED << mcs_lock, priority, ret_trylock, lock_, val_, 
                             lock_s, lock_sp, priority_level >>

sp4(self) == /\ pc[self] = "sp4"
             /\ IF ~val[self].pending
                   THEN /\ qspinlock' = [qspinlock EXCEPT ![lock[self]].pending = FALSE]
                   ELSE /\ TRUE
                        /\ UNCHANGED qspinlock
             /\ pc' = [pc EXCEPT ![self] = "queue"]
             /\ UNCHANGED << mcs_lock, priority, ret_trylock, stack, lock_, 
                             val_, lock_s, lock_sp, lock, val, old, next, prev, 
                             node, idx, cnt, priority_level >>

queue(self) == /\ pc[self] = "queue"
               /\ node' = [node EXCEPT ![self] = McsNode(self[1], 1)]
               /\ idx' = [idx EXCEPT ![self] = mcs_lock[node'[self]].count + 1]
               /\ mcs_lock' = [mcs_lock EXCEPT ![node'[self]].count = mcs_lock[node'[self]].count + 1]
               /\ pc' = [pc EXCEPT ![self] = "sp11"]
               /\ UNCHANGED << qspinlock, priority, ret_trylock, stack, lock_, 
                               val_, lock_s, lock_sp, lock, val, old, next, 
                               prev, cnt, priority_level >>

sp11(self) == /\ pc[self] = "sp11"
              /\ node' = [node EXCEPT ![self] = McsNode(self[1], idx[self])]
              /\ mcs_lock' = [mcs_lock EXCEPT ![node'[self]].locked = FALSE,
                                              ![node'[self]].next = NODE_ZERO]
              /\ /\ lock_sp' = [lock_sp EXCEPT ![self] = lock[self]]
                 /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "spin_trylock",
                                                          pc        |->  "sp13",
                                                          lock_sp   |->  lock_sp[self] ] >>
                                                      \o stack[self]]
              /\ pc' = [pc EXCEPT ![self] = "stl1"]
              /\ UNCHANGED << qspinlock, priority, ret_trylock, lock_, val_, 
                              lock_s, lock, val, old, next, prev, idx, cnt, 
                              priority_level >>

sp13(self) == /\ pc[self] = "sp13"
              /\ IF ret_trylock[self]
                    THEN /\ pc' = [pc EXCEPT ![self] = "release"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "sp14"]
              /\ UNCHANGED << qspinlock, mcs_lock, priority, ret_trylock, 
                              stack, lock_, val_, lock_s, lock_sp, lock, val, 
                              old, next, prev, node, idx, cnt, priority_level >>

sp14(self) == /\ pc[self] = "sp14"
              /\ old' = [old EXCEPT ![self] = LockVal(FALSE, FALSE, qspinlock[lock[self]].tail_idx, qspinlock[lock[self]].tail_cpu)]
              /\ qspinlock' = [qspinlock EXCEPT ![lock[self]].tail_idx = idx[self],
                                                ![lock[self]].tail_cpu = self[1]]
              /\ next' = [next EXCEPT ![self] = NODE_ZERO]
              /\ pc' = [pc EXCEPT ![self] = "sp15"]
              /\ UNCHANGED << mcs_lock, priority, ret_trylock, stack, lock_, 
                              val_, lock_s, lock_sp, lock, val, prev, node, 
                              idx, cnt, priority_level >>

sp15(self) == /\ pc[self] = "sp15"
              /\ IF TAIL_MASK(old[self])
                    THEN /\ prev' = [prev EXCEPT ![self] = McsNode(old[self].tail_cpu, old[self].tail_idx)]
                         /\ mcs_lock' = [mcs_lock EXCEPT ![prev'[self]].next = node[self]]
                         /\ pc' = [pc EXCEPT ![self] = "sp16"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "sp18"]
                         /\ UNCHANGED << mcs_lock, prev >>
              /\ UNCHANGED << qspinlock, priority, ret_trylock, stack, lock_, 
                              val_, lock_s, lock_sp, lock, val, old, next, 
                              node, idx, cnt, priority_level >>

sp16(self) == /\ pc[self] = "sp16"
              /\ mcs_lock[node[self]].locked
              /\ next' = [next EXCEPT ![self] = mcs_lock[node[self]].next]
              /\ pc' = [pc EXCEPT ![self] = "sp18"]
              /\ UNCHANGED << qspinlock, mcs_lock, priority, ret_trylock, 
                              stack, lock_, val_, lock_s, lock_sp, lock, val, 
                              old, prev, node, idx, cnt, priority_level >>

sp18(self) == /\ pc[self] = "sp18"
              /\ ~qspinlock[lock[self]].locked /\ ~qspinlock[lock[self]].pending
              /\ val' = [val EXCEPT ![self] = qspinlock[lock[self]]]
              /\ pc' = [pc EXCEPT ![self] = "locked"]
              /\ UNCHANGED << qspinlock, mcs_lock, priority, ret_trylock, 
                              stack, lock_, val_, lock_s, lock_sp, lock, old, 
                              next, prev, node, idx, cnt, priority_level >>

locked(self) == /\ pc[self] = "locked"
                /\ IF val[self].tail_idx = idx[self] /\ val[self].tail_cpu = self[1]
                      THEN /\ old' = [old EXCEPT ![self] = qspinlock[lock[self]]]
                           /\ IF (qspinlock[lock[self]]) = val[self]
                                 THEN /\ qspinlock' = [qspinlock EXCEPT ![lock[self]] = LOCKED_VAL]
                                 ELSE /\ TRUE
                                      /\ UNCHANGED qspinlock
                           /\ IF old'[self] = val[self]
                                 THEN /\ pc' = [pc EXCEPT ![self] = "release"]
                                 ELSE /\ pc' = [pc EXCEPT ![self] = "sp21"]
                      ELSE /\ pc' = [pc EXCEPT ![self] = "sp21"]
                           /\ UNCHANGED << qspinlock, old >>
                /\ UNCHANGED << mcs_lock, priority, ret_trylock, stack, lock_, 
                                val_, lock_s, lock_sp, lock, val, next, prev, 
                                node, idx, cnt, priority_level >>

sp21(self) == /\ pc[self] = "sp21"
              /\ qspinlock' = [qspinlock EXCEPT ![lock[self]].locked = TRUE]
              /\ IF next[self] = NODE_ZERO
                    THEN /\ mcs_lock[node[self]].next # NODE_ZERO
                         /\ next' = [next EXCEPT ![self] = mcs_lock[node[self]].next]
                    ELSE /\ TRUE
                         /\ next' = next
              /\ mcs_lock' = [mcs_lock EXCEPT ![next'[self]].locked = TRUE]
              /\ pc' = [pc EXCEPT ![self] = "release"]
              /\ UNCHANGED << priority, ret_trylock, stack, lock_, val_, 
                              lock_s, lock_sp, lock, val, old, prev, node, idx, 
                              cnt, priority_level >>

release(self) == /\ pc[self] = "release"
                 /\ mcs_lock' = [mcs_lock EXCEPT ![McsNode(self[1], 1)].count = mcs_lock[McsNode(self[1], 1)].count - 1]
                 /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                 /\ old' = [old EXCEPT ![self] = Head(stack[self]).old]
                 /\ next' = [next EXCEPT ![self] = Head(stack[self]).next]
                 /\ prev' = [prev EXCEPT ![self] = Head(stack[self]).prev]
                 /\ node' = [node EXCEPT ![self] = Head(stack[self]).node]
                 /\ idx' = [idx EXCEPT ![self] = Head(stack[self]).idx]
                 /\ cnt' = [cnt EXCEPT ![self] = Head(stack[self]).cnt]
                 /\ lock' = [lock EXCEPT ![self] = Head(stack[self]).lock]
                 /\ val' = [val EXCEPT ![self] = Head(stack[self]).val]
                 /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                 /\ UNCHANGED << qspinlock, priority, ret_trylock, lock_, val_, 
                                 lock_s, lock_sp, priority_level >>

spin_lock_slowpath(self) == sp1(self) \/ sp1_1(self) \/ sp1_2(self)
                               \/ sp2(self) \/ sp3(self) \/ sp4(self)
                               \/ queue(self) \/ sp11(self) \/ sp13(self)
                               \/ sp14(self) \/ sp15(self) \/ sp16(self)
                               \/ sp18(self) \/ locked(self) \/ sp21(self)
                               \/ release(self)

t1(self) == /\ pc[self] = "t1"
            /\ priority_level' = [priority_level EXCEPT ![self] = priority[self[1]]]
            /\ priority' = [priority EXCEPT ![self[1]] = self[2]]
            /\ /\ lock_' = [lock_ EXCEPT ![self] = Lock(self)]
               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "spin_lock",
                                                        pc        |->  "cs",
                                                        val_      |->  val_[self],
                                                        lock_     |->  lock_[self] ] >>
                                                    \o stack[self]]
            /\ val_' = [val_ EXCEPT ![self] = defaultInitValue]
            /\ pc' = [pc EXCEPT ![self] = "sl1"]
            /\ UNCHANGED << qspinlock, mcs_lock, ret_trylock, lock_s, lock_sp, 
                            lock, val, old, next, prev, node, idx, cnt >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ /\ lock_s' = [lock_s EXCEPT ![self] = Lock(self)]
               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "spin_unlock",
                                                        pc        |->  "t2",
                                                        lock_s    |->  lock_s[self] ] >>
                                                    \o stack[self]]
            /\ pc' = [pc EXCEPT ![self] = "su1"]
            /\ UNCHANGED << qspinlock, mcs_lock, priority, ret_trylock, lock_, 
                            val_, lock_sp, lock, val, old, next, prev, node, 
                            idx, cnt, priority_level >>

t2(self) == /\ pc[self] = "t2"
            /\ priority' = [priority EXCEPT ![self[1]] = priority_level[self]]
            /\ pc' = [pc EXCEPT ![self] = "t1"]
            /\ UNCHANGED << qspinlock, mcs_lock, ret_trylock, stack, lock_, 
                            val_, lock_s, lock_sp, lock, val, old, next, prev, 
                            node, idx, cnt, priority_level >>

thread(self) == t1(self) \/ cs(self) \/ t2(self)

Next == (\E self \in ProcSet:  \/ spin_lock(self) \/ spin_unlock(self)
                               \/ spin_trylock(self)
                               \/ spin_lock_slowpath(self))
           \/ (\E self \in THREADS: thread(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in THREADS : /\ WF_vars(thread(self))
                                 /\ WF_vars(spin_lock(self))
                                 /\ WF_vars(spin_unlock(self))
                                 /\ WF_vars(spin_trylock(self))
                                 /\ WF_vars(spin_lock_slowpath(self))

\* END TRANSLATION
=============================================================================

----------------------------- MODULE AsyncGameOfLife -----------------------------
EXTENDS Integers, FiniteSets
CONSTANT N
VARIABLE grid

ASSUME N \in Nat

vars == grid

RECURSIVE Sum(_, _)
Sum(f, S) == IF S = {} THEN 0
                       ELSE LET x == CHOOSE x \in S : TRUE
                            IN  f[x] + Sum(f, S \ {x})
                            
Pos == {<<x, y>> : x, y \in 1..N}
TypeOK == grid \in [Pos -> BOOLEAN]

\* Safe cell accessor that handles boundary conditions
sc[<<x, y>> \in (0 .. N + 1) \X (0 .. N + 1)] == 
    CASE \/ x = 0 \/ y = 0 \/ x > N \/ y > N -> 0
      [] <<x, y>> \in Pos /\ grid[<<x, y>>] -> 1
      [] OTHER -> 0

\* Calculate the number of live neighbors for a position
score(p) == LET nbrs == {x \in {-1, 0, 1} \X {-1, 0, 1} : x /= <<0, 0>>}
                points == {<<p[1] + x, p[2] + y>> : <<x, y>> \in nbrs}
            IN Sum(sc, points)

\* Game of Life rules: 
\* - Live cell with 2-3 neighbors survives
\* - Dead cell with exactly 3 neighbors becomes alive
\* - All other cells die or stay dead
ShouldLive(p) == \/ (grid[p] /\ score(p) \in {2, 3})
                 \/ (~grid[p] /\ score(p) = 3)

Init == grid \in [Pos -> BOOLEAN]

\* Asynchronous update: choose any cell and update it according to Game of Life rules
Next == \E p \in Pos : grid' = [grid EXCEPT ![p] = ShouldLive(p)]

Spec == Init /\ [][Next]_vars

=============================================================================

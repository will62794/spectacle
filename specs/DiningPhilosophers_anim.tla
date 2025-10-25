---- MODULE DiningPhilosophers_anim ----
EXTENDS TLC, SVG, DiningPhilosophers

\* Want sine and cosine to be in the same range as the coordinates.

Coords ==
  1 :> [x |-> 100, y |-> 50] @@
  2 :> [x |-> 70, y |-> 120] @@
  3 :> [x |-> 10, y |-> 100] @@
  4 :> [x |-> 10, y |-> 20]  @@
  5 :> [x |-> 70, y |-> 0]   @@

  7 :> [x |-> 85, y |-> 85]  @@ \* Between 1 and 2
  8 :> [x |-> 40, y |-> 110] @@ \* Between 2 and 3
  9 :> [x |-> 10, y |-> 60]  @@ \* Between 3 and 4
 10 :> [x |-> 40, y |-> 10]  @@ \* Between 4 and 5
  6 :> [x |-> 85, y |-> 25]     \* Between 5 and 1

F1 == "https://www.svgrepo.com/show/205326/fork.svg"
F2 == "https://www.svgrepo.com/show/424639/fork-food-kitchen.svg"

RingPhil == 
    [n \in P |-> Group(<<
        Rect(Coords[n].x, Coords[n].y, 20, 20,
            [rx |-> IF IsEating(n) THEN "0" ELSE "15", stroke |-> "black", opacity |-> "0.3", fill |-> "black"]),
         Text(Coords[n].x + 10, Coords[n].y + 15, ToString(n), ("fill" :> "black" @@ "text-anchor" :> "middle" @@ IF philosophers[n] # {} THEN [hidden |-> "true"] ELSE <<>>)),
         Image(Coords[n].x, Coords[n].y, 20, 20, F1, IF Cardinality(philosophers[n]) \in {1,2} THEN <<>> ELSE [hidden |-> "true"]),
         Image(Coords[n].x, Coords[n].y, 20, 20, F2, IF Cardinality(philosophers[n]) = 2 THEN <<>> ELSE [hidden |-> "true"])
     >>, <<>>)]

RingFork == 
    [n \in P |->Image(Coords[n+5].x, Coords[n+5].y, 20, 20, F1, IF n \in forks THEN <<>> ELSE [hidden |-> "true"])]

AnimView ==
    Group(RingPhil \o RingFork, 
        ("transform" :> "translate(20 20) scale(1.5 1.5)"))

\* Animation alias for generating SVG files with TLC.
AnimAlias ==
    [
        philosophers |-> philosophers, forks |-> forks
    ] @@
    [ _anim |-> SVGSerialize(SVGDoc(AnimView, 0, 0, 270, 270, <<>>), "DiningPhilosophers_anim_", TLCGet("level")) ]

====
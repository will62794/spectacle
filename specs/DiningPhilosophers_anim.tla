---- MODULE DiningPhilosophers_anim ----
EXTENDS TLC, DiningPhilosophers


\* 
\* Animation definitions.
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

-----

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

F1 == "https://www.svgrepo.com/download/205326/fork.svg"
F2 == "https://www.svgrepo.com/download/424639/fork-food-kitchen.svg"

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


====
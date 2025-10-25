----------------------------- MODULE AsyncGameOfLife_anim -----------------------------
EXTENDS TLC, Integers, FiniteSets, Sequences, SVG, IOUtils, TLCExt, AsyncGameOfLife

\* Constants for layout
CellSize == 20
GridOffset == 30

\* Convert position to screen coordinates
ScreenX(pos) == GridOffset + (pos[1] - 1) * CellSize
ScreenY(pos) == GridOffset + (pos[2] - 1) * CellSize

\* Create a simple cell visual element
CellElement(pos) == 
    LET x == ScreenX(pos)
        y == ScreenY(pos)
        isAlive == grid[pos]
    IN Rect(x, y, CellSize - 1, CellSize - 1, 
             (("fill" :> IF isAlive THEN "black" ELSE "white") @@
              "stroke" :> "gray" @@
              "stroke-width" :> "1"))

\* Create all cell elements as a simple sequence
CellElements == 
    LET positions == <<
        <<1,1>>, <<1,2>>, <<1,3>>,
        <<2,1>>, <<2,2>>, <<2,3>>,
        <<3,1>>, <<3,2>>, <<3,3>>
    >>
    IN [i \in DOMAIN positions |-> CellElement(positions[i])]

\* Grid border
GridBorder == Rect(GridOffset - 2, GridOffset - 2, 
                   N * CellSize + 4, N * CellSize + 4,
                   ("fill" :> "none" @@
                    "stroke" :> "black" @@
                    "stroke-width" :> "2"))

\* Title text
Title == Text(GridOffset + (N * CellSize) \div 2, GridOffset - 10,
              "Async Conway's Game of Life (N=" \o ToString(N) \o ")",
              ("text-anchor" :> "middle" @@
               "font-size" :> "16px" @@
               "font-weight" :> "bold" @@
               "fill" :> "black"))

\* Live cell count
LiveCells == Cardinality({p \in Pos : grid[p]})
Stats == Text(GridOffset, GridOffset + N * CellSize + 20,
              "Live cells: " \o ToString(LiveCells),
              ("font-size" :> "14px" @@
               "fill" :> "black"))

\* Animation view definition
AnimView == Group(<<Title, GridBorder, Stats>> \o CellElements, 
                  ("transform" :> "translate(10, 10)"))

\* Animation alias for generating SVG files
AnimAlias ==
    [
        grid |-> grid
    ] @@
    [ _anim |-> SVGSerialize(
                    SVGDoc(AnimView, -100, 0, N * CellSize + 300, N * CellSize + 120, <<>>),
                    "AsyncGameOfLife_anim_", TLCGet("level")) ]

=============================================================================

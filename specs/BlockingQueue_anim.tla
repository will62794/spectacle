---- MODULE BlockingQueue_anim ----
EXTENDS TLC, BlockingQueue

\*
\*
\* Animation stuff
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
     LET svgAttrs == ("x" :> x @@ "y" :> y) IN
     SVGElem("text", Merge(svgAttrs, attrs), <<>>, text) 
 
 \* Circle element. 'cx', 'cy', and 'r' should be given as integers.
 Circle(cx, cy, r, attrs) == 
     LET svgAttrs == ("cx" :> cx @@ "cy" :> cy @@ "r" :> r) IN
     SVGElem("circle", Merge(svgAttrs, attrs), <<>>, "")
 
 \* Rectangle element. 'x', 'y', 'w', and 'h' should be given as integers.
 Rect(x, y, w, h, attrs) == 
     LET svgAttrs == ("x" :> x @@ "y" :> y @@ "width" :> w @@ "height" :> h) IN
     SVGElem("rect", Merge(svgAttrs, attrs), <<>>, "")
 
 \* Group element. 'children' is as a sequence of elements that will be contained in this group.
 Group(children, attrs) == SVGElem("g", attrs, children, "")
 
 Injective(f) == \A x, y \in DOMAIN f : f[x] = f[y] => x = y
 
 SetToSeq(S) == CHOOSE f \in [1..Cardinality(S) -> S] : Injective(f)
 
\*  Empty == [a \in {} |-> {}] \* Cannot be <<>>, which is certainly a bug in Spectacle!!!

 \* Fix to the above issued in https://github.com/will62794/spectacle/commit/f84efe7
 Empty == <<>>
 
 \* The element of buffer at index i or empty string if i is out-of-bounds.
 ElemAt(i) == 
     IF i > Len(buffer) THEN "" ELSE buffer[i]
 
 --------------------------------
 
 \* Layout constants for better organization
 BUFFER_WIDTH == 45
 BUFFER_HEIGHT == 35
 CELL_SPACING == 8
 THREAD_RADIUS == 20
 THREAD_SPACING == 70
 BASE_X == 60
 BASE_Y == 80
 
 BufferCellColor(i) == 
     IF ElemAt(i) = "" THEN "#f8f9fa" ELSE "#17a2b8"
 
 BufferCell(i) == 
     LET x_pos == BASE_X + 150
         y_pos == BASE_Y + (i - 1) * (BUFFER_HEIGHT + CELL_SPACING)
         cell_content == IF ElemAt(i) = "" THEN "" ELSE ToString(ElemAt(i))
         text_color == IF ElemAt(i) = "" THEN "#6c757d" ELSE "white"
         value == Text(x_pos + 22, y_pos + 22, cell_content, 
                      ("text-anchor" :> "middle" @@ "font-family" :> "monospace" @@ "font-size" :> "12px" @@ "fill" :> text_color))
         rect  == Rect(x_pos, y_pos, BUFFER_WIDTH, BUFFER_HEIGHT, 
                      ("fill" :> BufferCellColor(i) @@ "stroke" :> "#495057" @@ "stroke-width" :> "2" @@ "rx" :> "3"))
         index_label == Text(x_pos - 8, y_pos + 22, ToString(i), 
                            ("text-anchor" :> "middle" @@ "font-family" :> "monospace" @@ "font-size" :> "10px" @@ "fill" :> "#6c757d"))
     IN Group(<<rect, value, index_label>>, <<>>)
 
 Buffer == [i \in 1..BufCapacity |-> BufferCell(i)]
 
 \* Buffer status indicator
 BufferStatus == 
     LET status_text == IF Len(buffer) = 0 THEN "EMPTY"
                       ELSE IF Len(buffer) = BufCapacity THEN "FULL"
                       ELSE ToString(Len(buffer)) \o " of " \o ToString(BufCapacity)
         x_pos == BASE_X + 150
         y_pos == BASE_Y + BufCapacity * (BUFFER_HEIGHT + CELL_SPACING) + 15
     IN Text(x_pos + 22, y_pos, status_text, 
            ("text-anchor" :> "middle" @@ "font-family" :> "monospace" @@ "font-weight" :> "bold" @@ 
             "font-size" :> "11px" @@ "fill" :> "#495057"))
 
 --------------------------------
 
 ThreadColor(t) == 
     IF t \in waitSet THEN "#dc3545"  \* Bootstrap red for waiting
     ELSE "#28a745"  \* Bootstrap green for active
 
 ThreadStatus(t) == 
     IF t \in waitSet THEN "WAIT" ELSE "RUN"
 
 ConsSeq == SetToSeq(Consumers)
 
 ConsumerCell(i) == 
     LET thread == ConsSeq[i]
         x_pos == BASE_X + 320
         y_pos == BASE_Y + (i - 1) * THREAD_SPACING
         circle == Circle(x_pos, y_pos, THREAD_RADIUS, 
                         ("fill" :> ThreadColor(thread) @@ "stroke" :> "#343a40" @@ "stroke-width" :> "2"))
         thread_label == Text(x_pos, y_pos - 3, ToString(thread), 
                             ("text-anchor" :> "middle" @@ "font-family" :> "monospace" @@ 
                              "font-size" :> "11px" @@ "font-weight" :> "bold" @@ "fill" :> "white"))
         status_label == Text(x_pos, y_pos + 8, ThreadStatus(thread), 
                             ("text-anchor" :> "middle" @@ "font-family" :> "monospace" @@ 
                              "font-size" :> "9px" @@ "fill" :> "white"))
     IN Group(<<circle, thread_label, status_label>>, <<>>)
 
 Cons == [i \in 1..Cardinality(Consumers) |-> ConsumerCell(i)]
 
 \* Consumer section label
 ConsumerLabel == Text(BASE_X + 320, BASE_Y - 30, "CONSUMERS", 
                     ("text-anchor" :> "middle" @@ "font-family" :> "monospace" @@ "font-weight" :> "bold" @@ 
                      "font-size" :> "12px" @@ "fill" :> "#495057"))
 
 --------------------------------
 
 ProdSeq == SetToSeq(Producers)
 
 ProducerCell(i) == 
     LET thread == ProdSeq[i]
         x_pos == BASE_X
         y_pos == BASE_Y + (i - 1) * THREAD_SPACING
         circle == Circle(x_pos, y_pos, THREAD_RADIUS, 
                         ("fill" :> ThreadColor(thread) @@ "stroke" :> "#343a40" @@ "stroke-width" :> "2"))
         thread_label == Text(x_pos, y_pos - 3, ToString(thread), 
                             ("text-anchor" :> "middle" @@ "font-family" :> "monospace" @@ 
                              "font-size" :> "11px" @@ "font-weight" :> "bold" @@ "fill" :> "white"))
         status_label == Text(x_pos, y_pos + 8, ThreadStatus(thread), 
                             ("text-anchor" :> "middle" @@ "font-family" :> "monospace" @@ 
                              "font-size" :> "9px" @@ "fill" :> "white"))
     IN Group(<<circle, thread_label, status_label>>, <<>>)
 
 Prod == [i \in 1..Cardinality(Producers) |-> ProducerCell(i)]
 
 \* Producer section label
 ProducerLabel == Text(BASE_X, BASE_Y - 30, "PRODUCERS", 
                     ("text-anchor" :> "middle" @@ "font-family" :> "monospace" @@ "font-weight" :> "bold" @@ 
                      "font-size" :> "12px" @@ "fill" :> "#495057"))
 
 \* Buffer section label
 BufferLabel == Text(BASE_X + 172, BASE_Y - 30, "BUFFER", 
                    ("text-anchor" :> "middle" @@ "font-family" :> "monospace" @@ "font-weight" :> "bold" @@ 
                     "font-size" :> "12px" @@ "fill" :> "#495057"))
 
 \* Add visual arrows showing data flow
 FlowArrows == 
     LET arrow1 == Text(BASE_X + 105, BASE_Y + 10, "→", 
                       ("text-anchor" :> "middle" @@ "font-size" :> "18px" @@ "fill" :> "#6c757d"))
         arrow2 == Text(BASE_X + 245, BASE_Y + 10, "→", 
                       ("text-anchor" :> "middle" @@ "font-size" :> "18px" @@ "fill" :> "#6c757d"))
     IN Group(<<arrow1, arrow2>>, <<>>)
 
 AnimView == 
     Group(<<ProducerLabel, BufferLabel, ConsumerLabel, BufferStatus, FlowArrows>> \o 
           Prod \o Buffer \o Cons, 
           ("transform" :> "scale(1.2) translate(30 20)"))


====
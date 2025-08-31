---- MODULE counter ----
EXTENDS TLC, Naturals

VARIABLE xval

Init == xval = 0
Next == xval' = xval + 1



====
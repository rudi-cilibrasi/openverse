# (#283) Return frames where the first success is taken and the clauses print
# or change an object: the call and the clauses after it run as a function
# of their own, recursive, which takes the continuation the frames are pushed
# on, so each alternative and each call is a failure context of its own: only
# the path to the value taken keeps its effects.
Walk(N:int)<transacts><decides>:int =
    Print("enter {N}")
    N > 0
    X := Walk[N - 1] | N
    Print("at {N} got {X}")
    X + 1
box := class:
    var N:int = 0
Fill(B:box, K:int)<transacts><decides>:int =
    K > 0
    set B.N += 1
    X := Fill[B, K - 1] | 0
    set B.N += 100
    X + B.N
Main()<transacts>:void =
    for (V := Walk[2]) { Print("v {V}") }
    if (V := Walk[2], V > 2) then Print("first {V}")
    if (V := Walk[2], V > 5) then Print("never") else Print("none")
    B := box{}
    for (V := Fill[B, 2]) { Print("v {V} n {B.N}") }
    C := box{}
    if (V := Fill[C, 2], V > 300) then Print("first {V} n {C.N}")
    D := box{}
    if (V := Fill[D, 2], V > 400) then Print("never") else Print("none n {D.N}")
    var Tries:int = 0
    if (X := Walk[3], set Tries += 1, X >= 3) then Print("first {X} after {Tries}")

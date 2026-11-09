# Review of #338: continuations only where the alternatives' values have one
# type (subclasses: copied), keyed by the captured names' types too (a for's
# body copied once per alternative); not called from a function of its own
# of a lazily taken call that allows fewer effects (copied there); and the
# continuations inside every alternative asked for in the first elaboration,
# so that nesting through inlined functions takes no more elaborations
base := class:
    K : int
ca := class(base) {}
cb := class(base) {}
MkA(K:int):ca = ca{K := K} | ca{K := K + 1}
Two(X:int):int = X | X + 1
TwoC(X:int)<computes>:int = X | X + 1
Nat(N:int)<computes><decides>:int =
    Print("at {N}")
    N | Nat[N + 1]
G1(B:int):int =
    Q := B | B + 50
    if (X := (Two(Q) | Two(Q + 1)), Y := (Two(10) | Two(20)), X + Y > 70) then X + Y else Q
G2(B:int):int =
    Q := B | B + 50
    if (X := (Two(Q) | G1(Q)), Y := (Two(10) | Two(20)), X + Y > 70) then X + Y else Q
G3(B:int):int =
    Q := B | B + 50
    if (X := (Two(Q) | G2(Q)), Y := (Two(10) | Two(20)), X + Y > 70) then X + Y else Q
G4(B:int):int =
    Q := B | B + 50
    if (X := (Two(Q) | G3(Q)), Y := (Two(10) | Two(20)), X + Y > 70) then X + Y else Q
Main():void =
    B : cb = cb{K := 7}
    if (X := (MkA(1) | B), Y := (Two(10) | Two(20)), X.K + Y > 26):
        Print("a {X.K} {Y}")
    for (X := (MkA(1) | B)):
        if (Y := (Two(10) | Two(20)), Z := (Two(1) | Two(2)), X.K + Y + Z > 26):
            Print("b {X.K} {Y} {Z}")
    if (N := Nat[0], X := (TwoC(1) | TwoC(3)), Y := (TwoC(10) | TwoC(30)), N + X + Y > 35):
        Print("c {N} {X} {Y}")
    if (X := (Two(1) | G4(1)), Y := (Two(10) | Two(20)), X + Y > 70):
        Print("d {X} {Y}")

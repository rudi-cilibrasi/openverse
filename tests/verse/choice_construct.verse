# Choices inside a struct or class construction (#283): its field values
# lifted as a call's arguments, in the order the construction evaluates
# them, its type's declaration order
pt := struct { X : int; Y : int }
G(S : string, V : int)<transacts>:int =
    Print(S)
    V
box := class:
    V : int
    W : int = 5
    block:
        Print("made {V}")
pair(t : type) := struct { A : t; B : t }
dflt := struct { X : int; Y : int = 7; Z : int }
Upto(N : int, M : int)<transacts>:int = if (N < M) then (N | Upto(N + 1, M)) else N
Digit():int = 0 | 1
Main()<transacts>:void =
    for (P := pt{X := 1 | 2, Y := 10 | 20}):
        Print("{P.X} {P.Y}")
    # written out of declaration order: X's value first, as without a choice
    P0 := pt{Y := G("y", 2), X := G("x", 1)}
    Print("{P0.X} {P0.Y}")
    for (P := pt{Y := G("y", 2), X := G("x", 1) | 3}):
        Print("{P.X} {P.Y}")
    # a class: its block: after the fields
    for (B := box{V := 1 | 2}):
        Print("{B.V} {B.W}")
    for (P := pair(int){B := 3 | 4, A := 1 | 2}):
        Print("{P.A} {P.B}")
    # a field not given whose default is a literal
    for (P := dflt{Z := 1 | 2, X := 0}):
        Print("{P.X} {P.Y} {P.Z}")
    # calls of functions with several values
    for (P := pt{Y := Upto(1, 2), X := Digit()}):
        Print("p {P.X} {P.Y}")
    if (Q := pt{X := Upto(1, 5), Y := 0}, Q.X > 3):
        Print("q {Q.X}")

shape(t:type) := class:
    K:int
    Sizes()<transacts>:int = K | K + 1
    Add(N:int)<transacts>:int = K + N | K + N + 100
big := class(shape(int)):
    Sizes<override>()<transacts>:int = 1000
    Add<override>(N:int)<transacts>:int = N * 2
G(S:string, O:shape(int))<transacts>:shape(int) =
    Print(S)
    O
H(O:shape(int))<transacts>:int =
    Print("h")
    O.Sizes()
Main()<transacts>:void =
    B := big{K := 1}
    S := shape(int){K := 1}
    for (A := G("a", B), X := A.Sizes(), X > 5000) { Print("never") }
    for (X := B.Sizes(), Y := S.Sizes(), X + Y > 1001) { Print("xy {X} {Y}") }
    for (Z := S.Add(B.Sizes()), Z > 1001) { Print("z {Z}") }
    for (Z := B.Add(S.Sizes())) { Print("w {Z}") }
    if (X := B.Sizes(), X > 999) { Print("if {X}") }
    if (X := S.Sizes(), X > 1) { Print("if2 {X}") }
    for (A := G("b", S), X := A.Sizes(), X > 1) { Print("x {X}") }
    for (X := H(B) + H(S), X > 1001) { Print("x {X}") }
    if (X := H(S) + H(S), X > 3) { Print("if {X}") }
    for (O := (S | B), X := O.Sizes(), X > 1) { Print("o {X}") }

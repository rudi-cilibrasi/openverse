# alternatives of a set's choice with several values or clauses of their own (#283): each runs the assignment itself, at the type of what set writes (a refinement, a class), after the path's indices, evaluated once; rolled back with the alternative where the first success is taken
nonneg := type{_X:int where 0 <= _X}
animal := class { Name:string = "a" }
dog := class(animal) { Barks:int = 3 }
cat := class(animal) { Lives:int = 9 }
holder := class { var F:int = 0 }
D():int = 1 | 2
Small():nonneg = 1 | 2
Pets():animal = dog{} | cat{}
Get(A:[]int, I:int):int = if (V := A[I]) then V else -1
Upto(A:int, B:int)<transacts><decides>:int =
    A <= B
    Print("visit {A}")
    A | Upto[A + 1, B]
Tell(S:string, X:int)<transacts>:int =
    Print(S)
    X
Main()<transacts>:void =
    var P:nonneg = 0
    for (set P = Small() | 7) { Print("p {P}") }
    var O:?int = false
    for (set O = (if (D() > 1) then option{D()} else false) | false) { Print("o {if (V := O?) then V else -1}") }
    var Pet:animal = dog{}
    for (set Pet = Pets() | animal{}) { Print("pet {Pet.Name}") }
    var A:[]int = array{0, 0}
    for (set A[Tell("i", 1)] = D() | 7) { Print("a {Get(A, 0)} {Get(A, 1)}") }
    for (set A[0 | 1] = D() | 9) { Print("b {Get(A, 0)} {Get(A, 1)}") }
    H := holder{}
    for (set H.F = (D() + 10) | 3) { Print("h {H.F}") }
    var N:int = 0
    if (set N = (Tell("t", 1) + D()) | 9, N > 2) { Print("if {N}") }
    if (set N = Upto[1, 3] | 0, N > 2) { Print("upto {N}") }
    if (X := (set N = D() | 5), X > 4) { Print("macro {X} {N}") }
    var M:int = 0
    if (set M = D() | 5, M > 9) { Print("never") } else { Print("rolled back {M}") }
    Print("end {N}")

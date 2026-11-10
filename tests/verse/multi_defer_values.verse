# A function's own defer: in one with several values (#283): it runs as each value leaves the function,
# after the value; a value whose clauses fail runs none (its effects rolled back); several run last
# registered first; in methods, overrides, generic functions and methods, overloads, nested calls; and a
# var the defer: reads, at its last value
F()<transacts>:int =
    defer: Print("d")
    1 | 2
G(N:int)<transacts><decides>:int =
    Print("g{N}")
    defer: Print("g-a{N}")
    X := N | N + 10
    defer: Print("g-b{X}")
    X > 1
    X * 2
an := class:
    K:int
    Vals()<transacts>:int =
        defer: Print("an{K}")
        K | K + 1
bn := class(an):
    Vals<override>()<transacts>:int =
        defer: Print("bn{K}")
        K * 10 | K * 100
Pair(A:t, B:t where t:type)<transacts>:t =
    defer: Print("pair")
    A | B
Inner()<transacts>:int =
    defer: Print("in")
    1 | 2
Outer()<transacts>:int =
    defer: Print("out")
    Inner() + 100
Counted()<transacts>:int =
    var C:int = 0
    defer: Print("c={C}")
    set C = 5 | 6
    C
H(N:int)<transacts>:int =
    defer: Print("h{N}")
    if (N > 1) then { defer: Print("hb{N}"); W := N | N + 1; W } else N * 10
gbox(t:type) := class:
    A:t
    B:t
    Both()<transacts>:t =
        defer: Print("both")
        A | B
Two(N:int)<transacts>:int =
    defer: Print("two-int")
    N | N + 1
Two(S:string)<transacts>:string =
    defer: Print("two-str")
    S | S + "!"
Main()<transacts>:void =
    for (X := F()) { Print("{X}") }
    if (X := F(), X > 1) { Print("if {X}") }
    for (Y := G[1]) { Print("y {Y}") }
    for (X := block{ defer: Print("bd"); Z := 1 | 2; Z * 10 }) { Print("b {X}") }
    if (V := option{G[0]}?) { Print("o {V}") }
    As : []an = array{an{K := 1}, bn{K := 2}}
    for (A : As, V := A.Vals()) { Print("v {V}") }
    for (S := Pair("x", "y")) { Print("s {S}") }
    for (X := Outer()) { Print("o {X}") }
    for (X := Inner(), Y := Inner(), X < Y) { Print("xy {X} {Y}") }
    for (X := Counted()) { Print("k {X}") }
    for (X := H(1), Y := H(2)) { Print("xy {X} {Y}") }
    if (X := H(2), Y := H(3), X + Y > 6) { Print("if {X} {Y}") }
    for (V := gbox(string){A := "p", B := "q"}.Both()) { Print("g {V}") }
    for (V := Two(1)) { Print("i {V}") }
    for (V := Two("s")) { Print("s {V}") }

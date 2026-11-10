# Generic functions and generic classes' methods with several values and named parameters (#283):
# defaults typed by where they are (array{}, false) or using an earlier parameter, a type argument
# inferred from named arguments only, named arguments in any order or with a choice, first success,
# two calls in one clause list, an overridden generic method, a tuple argument
Pick(X:t, ?Y:t, ?Z:int = 0 where t:type)<transacts>:t =
    Print("pick {Z}")
    X | Y
Arr(Xs:[]t, ?Extra:[]t = array{} where t:type)<transacts>:int = Xs.Length | Xs.Length + Extra.Length
Opt(X:t, ?D:?t = false where t:type)<transacts>:t =
    if (V := D?) then (V | X) else X
gbox(t:type) := class:
    A:t
    With(?B:t, ?N:int = 1)<transacts>:t = A | B
Rep(X:t, ?Ys:[]t = array{X, X} where t:type)<transacts>:int = Ys.Length | Ys.Length * 10
Wrap(?V:t, ?W:t where t:type)<transacts>:t = V | W
Two(X:t, ?Y:t where t:type)<transacts>:t = X | Y
box(t:type) := class:
    A:t
    Get(?B:t, ?N:int = 2)<transacts>:t = A | B
sbox(t:type) := class(box(t)):
    Get<override>(?B:t, ?N:int = 2)<transacts>:t = B
Both(X:t, Y:t, ?Z:int = 0 where t:type)<transacts>:t = X | Y
Main()<transacts>:void =
    for (V := Pick(1, ?Y := 2)) { Print("a {V}") }
    for (V := Pick("x", ?Z := 5, ?Y := "y")) { Print("b {V}") }
    for (N := Arr(array{1, 2})) { Print("c {N}") }
    for (N := Arr(array{1}, ?Extra := array{7, 8})) { Print("d {N}") }
    for (V := Opt(3)) { Print("e {V}") }
    for (V := Opt(3, ?D := option{9})) { Print("f {V}") }
    for (V := gbox(string){A := "p"}.With(?B := "q")) { Print("g {V}") }
    if (V := Pick(10, ?Y := 20), V > 10) { Print("h {V}") }
    for (N := Rep(5)) { Print("a {N}") }
    for (N := Rep("s", ?Ys := array{"t"})) { Print("b {N}") }
    for (V := Wrap(?W := "w", ?V := "v")) { Print("c {V}") }
    for (V := Two(1, ?Y := 2 | 3)) { Print("d {V}") }
    for (X := Two(1, ?Y := 2), Y := Two(10, ?Y := 20)) { Print("e {X} {Y}") }
    Bs : []box(int) = array{box(int){A := 1}, sbox(int){A := 2}}
    for (B : Bs, V := B.Get(?B := 7)) { Print("f {V}") }
    P := (1, 2)
    for (V := Both(P)) { Print("t {V}") }
    for (V := Both(("a", "b"))) { Print("u {V}") }

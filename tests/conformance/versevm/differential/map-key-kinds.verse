# Map keys of several comparable kinds: string, char, logic, tuple, enum,
# and lookups with an equal key made another way.
# Tests LANGUAGE.md, Maps: "[k]v (a comparable key with no array or map in
# it, through its options, tuples and a struct's fields, but string)".
# OpenVerse prints (Lean and C agree):
#   found 1 2 3 5 6 7 | missing missing missing
hue := enum:
    Red
    Green

Main():void =
    S:[string]int = map{"ab" => 1, "" => 2}
    C:[char]int = map{'x' => 3}
    L:[logic]int = map{true => 4, false => 5}
    T:[tuple(int, string)]int = map{(1, "a") => 6}
    E:[hue]int = map{hue.Green => 7}
    if (A := S["a" + "b"], B := S[""], D := C['x'], F := L[false], G := T[(0 + 1, "a")], H := E[hue.Green]):
        Print("OVPROBE found {A} {B} {D} {F} {G} {H}")
    P := if (T[(1, "b")]) then "found" else "missing"
    Q := if (E[hue.Red]) then "found" else "missing"
    Print("OVPROBE missing {P} {Q}")

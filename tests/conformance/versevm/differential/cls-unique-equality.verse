# <unique> classes compare by identity: an instance equals itself and an
# alias of it, and not another instance with the same fields; as map keys.
# Tests LANGUAGE.md, Classes, <unique>: "A <unique> class (and every class
# below it) is comparable: = and <> test identity, so two instances with
# equal fields differ, and an alias equals its original". Each letter: y the
# comparison succeeded, n it failed.
# OpenVerse prints (Lean and C agree):
#   y n y map 2 30
token := class<unique>:
    Id:int = 0

Main():void =
    A := token{Id := 1}
    B := token{Id := 1}
    C := A
    P := if (A = C) then "y" else "n"
    Q := if (A = B) then "y" else "n"
    R := if (A <> B) then "y" else "n"
    var M:[token]int = map{}
    if (set M[A] = 10, set M[B] = 20, set M[C] = 30) {}
    V := M[A] or -1
    Print("OVPROBE {P} {Q} {R} map {M.Length} {V}")

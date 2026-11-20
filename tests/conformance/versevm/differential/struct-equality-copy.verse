# Structs: field defaults, equality by value, nested structs, and a struct
# copied before the variable holding it is replaced.
# Tests LANGUAGE.md, Supported, Structs: "structural equality (a struct is
# the tuple of its fields in Verse Core)"; struct values are copied. Each
# letter: y the comparison succeeded, n it failed.
# OpenVerse prints (Lean and C agree):
#   5 0 1 2 eq y y y y 1
pt := struct:
    X:int = 0
    Y:int = 0

seg := struct:
    From:pt
    To:pt

Main():void =
    var A:pt = pt{X := 1, Y := 2}
    B := A
    set A = pt{X := 5}
    P := if (B = pt{X := 1, Y := 2}) then "y" else "n"
    Q := if (A = pt{X := 5, Y := 0}) then "y" else "n"
    R := if (A <> B) then "y" else "n"
    S:seg = seg{From := pt{}, To := pt{X := 1}}
    T := if (S = seg{From := pt{}, To := pt{X := 1, Y := 0}}) then "y" else "n"
    Print("OVPROBE {A.X} {A.Y} {B.X} {B.Y} eq {P} {Q} {R} {T} {S.To.X}")

# Options: query, or-default, nested options, and setting an option var.
# Tests LANGUAGE.md, Readings, "? on other values": "only logic and ?t";
# Failure: the left of or is a failure context.
# OpenVerse prints (Lean and C agree):
#   a 5 7 none 12 | b 3 outer some inner none
Main():void =
    O:?int = option{5}
    E:?int = false
    A := O? or 0
    B := E? or 7
    C := if (E?) then "some" else "none"
    var V:?int = false
    set V = option{A + B}
    D := V? or -1
    Print("OVPROBE a {A} {B} {C} {D}")
    NN:??int = option{option{3}}
    NE:??int = option{false}
    F := NN?? or -1
    G := if (Inner := NE?) then "outer some" else "outer none"
    H := if (NE??) then "inner some" else "inner none"
    Print("OVPROBE b {F} {G} {H}")

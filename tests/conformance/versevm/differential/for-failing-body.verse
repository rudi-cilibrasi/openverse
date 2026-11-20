# A for whose body can fail, inside a condition: does one failing iteration
# fail the whole for (and so the condition), or only skip itself?
# Tests LANGUAGE.md, Readings, "A failing for body": "unspecified (VC: the
# for fails)"; openverse: "the for fails (as in VC)" (the readings audit:
# Option.versetest:118 makes a failable body the enclosing context's).
# Epic's compiler may refuse a failable body. If an iteration were only
# skipped, a would print 2 elements.
# OpenVerse prints (Lean and C agree):
#   a failed b ok 3
Main():void =
    A:[]int = array{1, 2, 3}
    R := if (B := for (X : A) { A[X] }) then "ok {B.Length}" else "failed"
    S := if (C := for (X : A) { A[X - 1] }) then "ok {C.Length}" else "failed"
    Print("OVPROBE a {R} b {S}")

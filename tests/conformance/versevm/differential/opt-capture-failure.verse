# option{...} captures a failure: the empty option, with what the failed
# body wrote undone; a successful body keeps its writes.
# Tests LANGUAGE.md, Failure: "failure contexts (... option{} ...) with
# rollback of var writes"; Readings, "Output inside a failed failure
# context" (no Print in a failing body here).
# OpenVerse prints (Lean and C agree):
#   -1 4 N 10 | logic true false
Positive(X:int)<computes><decides>:int = X > 0

Main():void =
    var N:int = 0
    A:?int = option{set N += 1; Positive[-3]}
    B:?int = option{set N += 10; Positive[4]}
    X := A? or -1
    Y := B? or -1
    Print("OVPROBE {X} {Y} N {N}")
    L:logic = logic{Positive[2]}
    M:logic = logic{Positive[-2]}
    P := if (L?) then "true" else "false"
    Q := if (M?) then "true" else "false"
    Print("OVPROBE logic {P} {Q}")

# Book: Tests/LiveVariables.versetest:128 (live variables, docs/15_live_variables.md,
# an unreleased feature).
Main():void =
    var X:int = 0
    var Y:int = 0
    set live X = Y
    set Y = 1
    Print("OVPROBE live {X}")

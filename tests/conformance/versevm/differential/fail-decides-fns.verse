# <decides> functions: success values, failure, writes undone when the
# function fails, and calls in or chains and in for filters.
# Tests LANGUAGE.md, Functions: "<decides> (called with F[...])"; Failure:
# "<decides> bodies" are failure contexts.
# OpenVerse prints (Lean and C agree):
#   5 4 3 log 1 | first 3
store := class:
    var Trail:[]int = array{}

Half(X:int)<computes><decides>:int =
    Mod[X, 2] = 0
    Quotient[X, 2]

Record(S:store, X:int)<transacts><decides>:int =
    set S.Trail += array{X}
    X > 0
    X

Main():void =
    A:int = Half[7] or Half[10] or 0
    Halves := for (X := 1..8, H := Half[X]) { H }
    S := store{}
    R:int = Record[S, -1] or Record[S, 3] or 0
    if (Record[S, 5], Record[S, -6]) {}
    Print("OVPROBE {A} {Halves.Length} {R} log {S.Trail.Length}")
    if (L0 := S.Trail[0]):
        Print("OVPROBE first {L0}")

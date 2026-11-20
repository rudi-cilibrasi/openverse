# Evaluation order of a set's index, key and value, and of a compound set's
# parts, recorded in a log.
# Tests LANGUAGE.md, Supported, Mutation: "indices and keys evaluated once,
# left to right, then the new value, then the variable rebuilt (for op=, the
# old value is read after the new one ...)" (#704, settled on Epic for the
# compound cases by the compound-* probes; this probe asks the plain order).
# OpenVerse prints (Lean and C agree):
#   107 15 234 values 7 15 7
trace := class:
    var Trail:string = ""

Mark(T:trace, N:int)<transacts>:int =
    set T.Trail += "{N}"
    N

Main():void =
    T := trace{}
    var G:[][]int = array{array{0, 0}, array{0, 0}}
    if (set G[Mark(T, 1)][Mark(T, 0)] = Mark(T, 7)) {}
    set T.Trail += " "
    var M:[int]int = map{1 => 10}
    if (set M[Mark(T, 1)] += Mark(T, 5)) {}
    set T.Trail += " "
    var A:[]int = array{0, 0, 0}
    if (set A[Mark(T, 2)] = Mark(T, 3) + Mark(T, 4)) {}
    if (G10 := G[1][0], M1 := M[1], A2 := A[2]):
        Print("OVPROBE {T.Trail} values {G10} {M1} {A2}")

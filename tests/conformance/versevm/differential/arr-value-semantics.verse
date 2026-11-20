# Arrays are values: a copy taken before a set keeps the old elements, also
# an array stored inside another array or a tuple.
# Tests LANGUAGE.md, Supported: arrays are values ("set A[i] = e" rebuilds
# the variable); Mutation: "then the variable rebuilt".
# OpenVerse prints (Lean and C agree):
#   100,2,300 1,2,3 100,200,3 100,2,3 100,2,3
Show(A:[]int):string = Join(for (X : A) { "{X}" }, ",")

Main():void =
    var A:[]int = array{1, 2, 3}
    B := A
    if (set A[0] = 100) {}
    var G:[][]int = array{A, A}
    T := (A, 5)
    if (set G[0][1] = 200) {}
    if (set A[2] = 300) {}
    if (G0 := G[0], G1 := G[1]):
        Print("OVPROBE {Show(A)} {Show(B)} {Show(G0)} {Show(G1)} {Show(T(0))}")

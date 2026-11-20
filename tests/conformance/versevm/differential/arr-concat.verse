# Array concatenation with +, Concatenate of several arrays, and empty
# arrays on either side.
# Tests LANGUAGE.md, Array methods: "Concatenate(A, B, ...) or
# Concatenate(Arrays)"; Epic's digest: Concatenate(Arrays:[][]t); Equality:
# "An empty array{} ... with no type from its context ... A + array{1} is a
# []int".
# OpenVerse prints (Lean and C agree):
#   a 1,2,3,1,2 1,2 1,2 0 | b 1,2,9,1,2 5 | c 2 1,2,7
Show(A:[]int):string = Join(for (X : A) { "{X}" }, ",")

Main():void =
    A:[]int = array{1, 2}
    E:[]int = array{}
    B := A + array{3} + A
    Print("OVPROBE a {Show(B)} {Show(E + A)} {Show(A + E)} {(E + E).Length}")
    C := Concatenate(array{A, E, array{9}, A})
    Print("OVPROBE b {Show(C)} {C.Length}")
    D:[][]int = array{A} + array{array{7}}
    Print("OVPROBE c {D.Length} {Show(Concatenate(D))}")

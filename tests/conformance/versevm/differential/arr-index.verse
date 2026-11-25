# Array indexing: in range, out of range, negative, nested, and in an or.
# Tests LANGUAGE.md, Supported: indexing "A[i]" fails out of range;
# Failure: an index is a failure context's expression.
# OpenVerse prints (Lean and C agree):
#   in 10 30 3 | out fails fails -1 | nested 3 3 | empty row fails
Main():void =
    A:[]int = array{10, 20, 30}
    if (X := A[0], Y := A[2]):
        Print("OVPROBE in {X} {Y} {A.Length}")
    P := if (A[3]) then "ok" else "fails"
    Q := if (A[-1]) then "ok" else "fails"
    R:int = A[5] or -1
    Print("OVPROBE out {P} {Q} {R}")
    G:[][]int = array{array{1, 2}, array{}, array{3}}
    if (Z := G[2][0]):
        Print("OVPROBE nested {Z} {G.Length}")
    S := if (G[1][0]) then "ok" else "fails"
    Print("OVPROBE empty row {S}")

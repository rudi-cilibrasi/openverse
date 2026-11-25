# Writes to vars, array elements, map entries and object fields in a
# condition that fails are undone; in one that succeeds, kept.
# Tests LANGUAGE.md, Failure: "failure contexts (if conditions, ...) with
# rollback of var writes"; ch. 8 (08_failure.md:147): changes "only become
# permanent if the entire context succeeds".
# OpenVerse prints (Lean and C agree):
#   failed 1 2 1 0 | kept 3 9 5 7
box := class:
    var V:int = 0

Main():void =
    var X:int = 1
    var A:[]int = array{1, 2}
    var M:[int]int = map{1 => 1}
    B := box{}
    if (set X = 2, set A[0] = 9, set M[2] = 5, set B.V = 7, X > 5) {}
    Print("OVPROBE failed {X} {A.Length} {M.Length} {B.V}")
    if (set X = 3, set A[0] = 9, set M[2] = 5, set B.V = 7, X > 2) {}
    if (A0 := A[0], M2 := M[2]):
        Print("OVPROBE kept {X} {A0} {M2} {B.V}")

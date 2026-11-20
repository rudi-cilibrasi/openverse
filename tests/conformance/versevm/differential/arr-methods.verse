# Array methods that make new arrays: Slice, Remove, RemoveElement, Insert,
# ReplaceElement, Find, Last; the original is unchanged.
# Tests LANGUAGE.md, Array methods ("all failable"); Epic's digest gives
# each one's bounds. Arrays print as their elements joined by commas.
# OpenVerse prints (Lean and C agree):
#   a 6,7 5,8,9 6,7,8,9 5,6,0,0,7,8,9 5,6,7,8,9 | b 5,6,7,8,1 2 9 8
#   c fails fails fails fails
Show(A:[]int):string = Join(for (X : A) { "{X}" }, ",")

Main():void =
    A:[]int = array{5, 6, 7, 8, 9}
    if (B := A.Slice[1, 3], C := A.Remove[1, 3], D := A.RemoveElement[0], E := A.Insert[2, array{0, 0}]):
        Print("OVPROBE a {Show(B)} {Show(C)} {Show(D)} {Show(E)} {Show(A)}")
    if (F := A.ReplaceElement[4, 1], G := A.Find[7], H := A.Last[], I := A.Last[1]):
        Print("OVPROBE b {Show(F)} {G} {H} {I}")
    J := if (A.Insert[6, array{1}]) then "ok" else "fails"
    K := if (A.Find[42]) then "ok" else "fails"
    L := if (A.Remove[3, 6]) then "ok" else "fails"
    M := if (A.Last[5]) then "ok" else "fails"
    Print("OVPROBE c {J} {K} {L} {M}")

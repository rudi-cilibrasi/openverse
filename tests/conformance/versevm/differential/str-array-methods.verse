# Array methods applied to strings: Find, Remove, Insert, Replace*, Join.
# Tests LANGUAGE.md, Array methods ("A.Find[x]", "A.RemoveFirstElement[x]",
# "A.Insert[i, B]", "A.ReplaceAllElements(x, y)", "A.ReplaceAll(Pattern,
# Replacement) (contiguous subarrays, left to right, not overlapping)") and
# Epic's digest ("only the position with the lowest index is replaced" when
# instances overlap); Join(Strings, Separator).
# OpenVerse prints (Lean and C agree):
#   a 2 bnana ban--ana bonana | b bununu baaa bXna bb | c [x, y, z] [] [solo]
Main():void =
    S:string = "banana"
    if (A := S.Find['n'], B := S.RemoveFirstElement['a'], C := S.Insert[3, "--"], D := S.ReplaceFirstElement['a', 'o']):
        Print("OVPROBE a {A} {B} {C} {D}")
    E := S.ReplaceAllElements('a', 'u')
    F := S.RemoveAllElements('n')
    G := S.ReplaceAll("ana", "X")
    H := "aaaa".ReplaceAll("aa", "b")
    Print("OVPROBE b {E} {F} {G} {H}")
    Print("OVPROBE c [{Join(array{"x", "y", "z"}, ", ")}] [{Join(array{}, "-")}] [{Join(array{"solo"}, "-")}]")

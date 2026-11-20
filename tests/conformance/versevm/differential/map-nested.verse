# Maps of arrays and arrays of maps: updates through nested paths.
# Tests LANGUAGE.md, Mutation: "paths ... set M[k].F = e", "an index out of
# range or a missing intermediate key fails, while the last key of a path
# inserts".
# OpenVerse prints (Lean and C agree):
#   a 9,2 4 fails | b 2 7 2
Show(A:[]int):string = Join(for (X : A) { "{X}" }, ",")

Main():void =
    var M:[int][]int = map{1 => array{1, 2}}
    if (set M[1][0] = 9) {}
    P := if (set M[2][0] = 5) then "ok" else "fails"
    if (set M[2] = array{4}) {}
    if (A := M[1], B := M[2]):
        Print("OVPROBE a {Show(A)} {Show(B)} {P}")
    var G:[][string]int = array{map{"k" => 1}}
    if (set G[0]["k"] += 1, set G[0]["n"] = 7) {}
    if (H := G[0], K := H["k"], N := H["n"]):
        Print("OVPROBE b {K} {N} {H.Length}")

# Map lookups that fail, compound updates of present and missing keys, and
# removing a key by rebuilding the map without it.
# Tests LANGUAGE.md, Maps: "M[k] (fails on a missing key)", "set M[k] op= v
# (fails on a missing key)", ".Length".
# OpenVerse prints (Lean and C agree):
#   a missing 2 fails a1,b12,c3 | b a1,c3 2 3
Keys(M:[string]int):string = Join(for (K -> V : M) { "{K}{V}" }, ",")

Main():void =
    var M:[string]int = map{"a" => 1, "b" => 2, "c" => 3}
    P := if (M["z"]) then "found" else "missing"
    Q := M["b"] or -1
    if (set M["b"] += 10) {}
    R := if (set M["q"] += 1) then "updated" else "fails"
    Print("OVPROBE a {P} {Q} {R} {Keys(M)}")
    var N:[string]int = map{}
    for (K -> V : M, K <> "b"):
        if (set N[K] = V) {}
    Print("OVPROBE b {Keys(N)} {N.Length} {M.Length}")

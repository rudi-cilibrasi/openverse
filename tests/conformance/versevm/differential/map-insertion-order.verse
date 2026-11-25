# Iteration order of a map: its literal's order, a new key set at the end,
# and an existing key overwritten in place.
# Tests LANGUAGE.md, Maps: "for (K -> V : M) in insertion order", "set
# M[k] = v (insert or update)", "order-sensitive equality (a map is the
# array of its pairs in Verse Core)". A hash map would iterate in another
# order.
# OpenVerse prints (Lean and C agree):
#   literal 3c,1a,2b | added 3c,1a,2b,0z | overwritten 3c,1A,2b,0z 4
#   more 3C,1A,2b,0z,-5n 5
Keys(M:[int]string):string = Join(for (K -> V : M) { "{K}{V}" }, ",")

Main():void =
    var M:[int]string = map{3 => "c", 1 => "a", 2 => "b"}
    Print("OVPROBE literal {Keys(M)}")
    if (set M[0] = "z") {}
    Print("OVPROBE added {Keys(M)}")
    if (set M[1] = "A") {}
    Print("OVPROBE overwritten {Keys(M)} {M.Length}")
    if (set M[-5] = "n", set M[3] = "C") {}
    Print("OVPROBE more {Keys(M)} {M.Length}")

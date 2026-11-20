# A map literal that gives one key twice: which value it keeps and where the
# key comes in the order.
# Tests LANGUAGE.md, Maps: "map{k => v, ...} (a key given twice keeps its
# last value, at its last position ...)". Other readings: the last value at
# the first position (1c,2b), or the first value (1a,2b).
# OpenVerse prints (Lean and C agree):
#   2b,1c 2 | 5z,6w 2
Keys(M:[int]string):string = Join(for (K -> V : M) { "{K}{V}" }, ",")

Main():void =
    M:[int]string = map{1 => "a", 2 => "b", 1 => "c"}
    Print("OVPROBE {Keys(M)} {M.Length}")
    N:[int]string = map{5 => "x", 5 => "y", 5 => "z", 6 => "w"}
    Print("OVPROBE {Keys(N)} {N.Length}")

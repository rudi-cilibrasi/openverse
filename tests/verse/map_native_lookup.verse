# (#795) A map's lookup and the search of a key in `set M[k] = v` are the primitives mapGet and
# mapFind: the first pair whose key equals the key, by Verse's equality. Keys of each comparable
# kind, a key given a second time (its value is replaced in place and its position kept), a key
# that is absent, a lookup that fails inside a failure context, and keys equal though held
# differently (ints across 64 bits, tuples, strings built two ways).
color := enum{Red, Green, Blue}
Show(M:[int]int):string = Join(for (K -> V : M) { "{K}={V}" }, " ")
Main():void =
    var M:[int]int = map{}
    for (I := 1..5):
        if (set M[I * 10] = I) {}
    if (set M[30] = 33) {}
    if (set M[10] = 11) {}
    Print(Show(M))
    Print("{M[30] or -1} {M[50] or -1} {M[60] or -1} {M.Length}")
    if (V := M[20], W := M[V * 5]) then Print("chained: {V} {W}") else Print("chained: absent")
    if (not M[7]) then Print("7 is absent")
    var S:[string]int = map{"a" => 1, "bc" => 2}
    if (set S["b" + "c"] = 20, set S[""] = 0) {}
    Print("{S["bc"] or -1} {S["a"] or -1} {S[""] or -1} {S["abc"] or -1} {S.Length}")
    var T:[tuple(int, string)]string = map{(1, "x") => "one-x"}
    if (set T[(1, "y")] = "one-y", set T[(1, "x")] = "again") {}
    Print("{T[(1, "x")] or "?"} {T[(1, "y")] or "?"} {T[(2, "x")] or "?"} {T.Length}")
    var E:[color]int = map{color.Red => 1, color.Blue => 3}
    if (set E[color.Green] = 2) {}
    Print("{E[color.Red] or 0} {E[color.Green] or 0} {E[color.Blue] or 0}")
    var C:[char]int = map{'a' => 1}
    if (set C['b'] = 2, set C['a'] = 10) {}
    Print("{C['a'] or 0} {C['b'] or 0} {C['c'] or 0}")
    var L:[logic]string = map{true => "yes"}
    if (set L[false] = "no") {}
    Print("{L[true] or "?"} {L[false] or "?"}")
    Big:int = 9223372036854775807
    var B:[int]string = map{Big => "max", Big + 1 => "past", -Big - 2 => "below"}
    if (set B[Big * 2 - Big + 1] = "past again") {}
    Print("{B[Big] or "?"} / {B[Big + 1] or "?"} / {B[0 - Big - 2] or "?"} / {B[Big + 2] or "?"} / {B.Length}")
    var O:[?int]int = map{option{1} => 1, false => 0}
    if (set O[option{2}] = 2) {}
    Print("{O[option{1}] or -1} {O[false] or -1} {O[option{2}] or -1} {O[option{3}] or -1}")
    var Count:int = 0
    for (K -> V : M, W := M[K], W = V) { set Count += 1 }
    Print("every key finds its own value: {Count} of {M.Length}")

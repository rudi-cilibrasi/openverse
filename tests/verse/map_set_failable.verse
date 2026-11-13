# A set through a map's key can fail in Verse (the key's reference is
# <decides>, the Book of Verse's API reference), so it is written in a failure
# context; its last key inserts, so it succeeds, and its value is the value
# set (ch. 1). A plain variable's set cannot fail.
Main():void =
    var M:[string]int = map{}
    if (set M["a"] = 1) then Print("inserted {M.Length}")
    if (V := (set M["a"] = 5)) then Print("updated to {V}")
    # (as the left of or, which must be able to fail: the Book's own form)
    (set M["b"] = 2) or Err()
    for (K : array{"c", "d"}, set M[K] = 3) { Print("for {K}") }
    if (not (set M["x"] = 9)) then Print("never") else Print("not of a set fails")
    # (an intermediate key that is missing still fails the set)
    var N:[string][string]int = map{"o" => map{}}
    if (set N["o"]["i"] = 7) then Print("nested inserted")
    if (set N["missing"]["i"] = 7) then Print("never") else Print("missing outer key")
    var X:int = 0
    set X = 4
    for (K -> V : M) { Print("{K} {V}") }
    Print("{X}")

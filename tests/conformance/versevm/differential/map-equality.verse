# Equality of maps with the same pairs in another order, and of maps after
# an overwrite.
# Tests LANGUAGE.md, Maps: "order-sensitive equality (a map is the array of
# its pairs in Verse Core)". A set-like equality would give y for the
# reordered maps. Each letter: y the comparison succeeded, n it failed.
# OpenVerse prints (Lean and C agree):
#   same y reordered n overwritten y shorter y empty y
Main():void =
    A:[int]int = map{1 => 10, 2 => 20}
    B:[int]int = map{2 => 20, 1 => 10}
    var C:[int]int = map{1 => 0, 2 => 20}
    if (set C[1] = 10) {}
    P := if (A = map{1 => 10, 2 => 20}) then "y" else "n"
    Q := if (A = B) then "y" else "n"
    R := if (A = C) then "y" else "n"
    S := if (A <> map{1 => 10}) then "y" else "n"
    E:[int]int = map{}
    T := if (E = map{}) then "y" else "n"
    Print("OVPROBE same {P} reordered {Q} overwritten {R} shorter {S} empty {T}")

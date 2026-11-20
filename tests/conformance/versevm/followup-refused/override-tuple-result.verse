# Book: Tests/Bugs/FORT-642876-CollidingCoercedOverrideNames.versetest 86,
# 132, 158, 174 (4 cases): an override whose result is a tuple(int, int) where
# the overridden method, of a parametric class at []int, returns an array: an
# override at a coerced signature. The Book's tests expect them valid.
# OpenVerse (ce8632ea, Lean) refuses this probe: "pair_getter.Get must have
# the signature of getter.Get, which it overrides"
# If UEFN 43.12 admits it, it prints
#   length 2
# and OpenVerse has a gap on Verse that Epic ships; if it refuses it, the Book
# is ahead of the shipped compiler here and OpenVerse's refusal is Epic's.
# Control: override-tuple-result-control (the override at the overridden
# signature, []int).
getter(t:type) := class<abstract>:
    Get():t

pair_getter := class(getter([]int)):
    Get<override>():tuple(int, int) = (1, 2)

Main():void =
    X:getter([]int) = pair_getter{}
    Print("OVPROBE length {X.Get().Length}")

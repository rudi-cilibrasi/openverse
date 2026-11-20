# Book: Tests/CoercedOverrides.versetest 99, 103, 107, 111;
# Tests/Bugs/FORT-642876-CollidingCoercedOverrideNames.versetest:193 (5
# cases): an override taking one []int parameter where the overridden method
# takes two ints, called through the base class with two arguments. The Book's
# tests expect them valid.
# OpenVerse (ce8632ea, Lean) refuses this probe: "derived.Method must have the
# signature of base.Method, which it overrides"
# If UEFN 43.12 admits it, it prints
#   through base 2
# and OpenVerse has a gap on Verse that Epic ships; if it refuses it, the Book
# is ahead of the shipped compiler here and OpenVerse's refusal is Epic's.
base := class:
    Method(X:int, Y:int):int = X + Y

derived := class(base):
    Method<override>(X:[]int):int = X.Length

Main():void =
    B:base = derived{}
    Print("OVPROBE through base {B.Method(1, 2)}")

# Book: Tests/NestedNamedTupleParameters.versetest 18, 29, 39, 68, 82, 92,
# decls; Tests/Where.versetest:14 (8 cases): named parameters with defaults
# inside a tuple parameter, SumThree(U:int, (?X:int = 1, ?Y:int = 1)) (ch. 6,
# tuple parameters). The Book's tests expect them valid.
# OpenVerse (ce8632ea, Lean) refuses this probe: "a named parameter inside a
# tuple parameter (?X) is not supported yet"
# If UEFN 43.12 admits it, it prints
#   defaults 3 | given 6
# and OpenVerse has a gap on Verse that Epic ships; if it refuses it, the Book
# is ahead of the shipped compiler here and OpenVerse's refusal is Epic's.
SumThree(U:int, (?X:int = 1, ?Y:int = 1)):int = U + X + Y

Main():void =
    Print("OVPROBE defaults {SumThree(1, ())}")
    Print("OVPROBE given {SumThree(1, (?X := 2, ?Y := 3))}")

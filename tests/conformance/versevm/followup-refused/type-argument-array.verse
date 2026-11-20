# Book: Tests/TypeParam.versetest 18, 21, 24, 27, 32, 35, 38, 54;
# Tests/ParametricFunctions.versetest 464, 469, 490;
# Tests/GenerateFunctionForParametricInterface.versetest:10 (12 cases): a type
# that is not a name written as an argument, []int for a function's explicit
# t:type parameter (the Book's cases also write [int]int, ?int, int->int,
# tuple(int, int), subtype(c), type{...} and class2(int)). The Book's tests
# expect them valid.
# OpenVerse (ce8632ea, Lean) refuses this probe: "unexpected '['"
# If UEFN 43.12 admits it, it prints
#   outer 2
# and OpenVerse has a gap on Verse that Epic ships; if it refuses it, the Book
# is ahead of the shipped compiler here and OpenVerse's refusal is Epic's.
# Control: type-argument-array-control (the type argument a name, int).
Pair(t:type, X:t):[]t = array{X, X}

Main():void =
    A := Pair([]int, array{1, 2, 3})
    Print("OVPROBE outer {A.Length}")

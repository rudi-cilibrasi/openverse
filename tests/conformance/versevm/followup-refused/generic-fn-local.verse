# Book: Tests/ParametricFunctions.versetest:327 (1 case): a generic function
# bound to a local, F := Identity, then called. The Book's tests expect it
# valid.
# OpenVerse (ce8632ea, Lean) refuses this probe: "'Identity' is generic: a
# function type determining all its type arguments and satisfying its bounds
# must be expected (#214, #209)"
# If UEFN 43.12 admits it, it prints
#   value 1
# and OpenVerse has a gap on Verse that Epic ships; if it refuses it, the Book
# is ahead of the shipped compiler here and OpenVerse's refusal is Epic's.
Identity(X:t where t:type):t = X

Main():void =
    F := Identity
    Print("OVPROBE value {F(1)}")

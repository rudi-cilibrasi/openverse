# Book: Tests/Definitions.versetest:37;
# Tests/Attributes/CustomClassVarAccessors.versetest:642 (2 cases): a
# definition used as an expression, X:int = Y:int = 4, both names bound after
# it. The Book's tests expect them valid.
# OpenVerse (ce8632ea, Lean) refuses this probe: "unknown identifier 'Y'"
# If UEFN 43.12 admits it, it prints
#   x 4 y 4
# and OpenVerse has a gap on Verse that Epic ships; if it refuses it, the Book
# is ahead of the shipped compiler here and OpenVerse's refusal is Epic's.
Main():void =
    X:int = Y:int = 4
    Print("OVPROBE x {X} y {Y}")

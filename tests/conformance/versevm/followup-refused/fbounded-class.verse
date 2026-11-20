# Book: Tests/Bugs/FORT-642876-CollidingCoercedOverrideNames.versetest 23, 29,
# 34, 40, 46, decls (6 cases): a class that names itself in its parent's type
# argument, item := class(cloneable(item)) (an F-bounded class). The Book's
# tests expect them valid.
# OpenVerse (ce8632ea, Lean) refuses this probe: "the Verse Core type of class
# item would contain itself, through its type arguments (#63)"
# If UEFN 43.12 admits it, it prints
#   clone 13
# and OpenVerse has a gap on Verse that Epic ships; if it refuses it, the Book
# is ahead of the shipped compiler here and OpenVerse's refusal is Epic's.
# Control: fbounded-class-control (the parent's type argument another class).
cloneable(t:type) := interface:
    Clone()<transacts>:t

item := class(cloneable(item)):
    Value:int
    Clone<override>()<transacts>:item = item{Value := Value}

Main():void =
    X:cloneable(item) = item{Value := 13}
    Y := X.Clone()
    Print("OVPROBE clone {Y.Value}")

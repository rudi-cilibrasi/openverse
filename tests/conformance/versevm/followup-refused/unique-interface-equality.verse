# Book: Tests/ComparableInterface.versetest 5, 13, 26, 37 (4 cases): values of
# an interface<unique> that no class implements compared with =; compile only,
# as the Book's cases (OpenVerse admits the comparison once a class implements
# the interface: the control). The Book's tests expect them valid.
# OpenVerse (ce8632ea, Lean) refuses this probe: "an operand of '=' must be
# comparable, and shape is a class (only <unique> classes are comparable, by
# identity)"
# If UEFN 43.12 admits it, it prints
#   compiled
# and OpenVerse has a gap on Verse that Epic ships; if it refuses it, the Book
# is ahead of the shipped compiler here and OpenVerse's refusal is Epic's.
# Control: unique-interface-equality-control (a class implements the
# interface, and two of its objects are compared).
shape := interface<unique>:
    Sides():int

Same(A:shape, B:shape):logic = if (A = B) then true else false

Main():void =
    Print("OVPROBE compiled")

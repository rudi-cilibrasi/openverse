# Book: Tests/ComparableInterface.versetest 5, 13, 26, 37 (4 cases): values of
# an interface<unique> that no class implements compared with =; compile only,
# as the Book's cases (OpenVerse admits the comparison once a class implements
# the interface: the control). The Book's tests expect them valid.
# OpenVerse (ce8632ea, Lean) refused this probe: "an operand of '=' must be
# comparable, and shape is a class (only <unique> classes are comparable, by
# identity)"
# Epic's Verse VM (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086,
# 2026-11-20) admitted it and printed
#   compiled
# OpenVerse now prints it too (#724, Lean and C): a <unique> interface or
# class that no concrete class is below is comparable, as one with instances
# is (tests/verse/unique_interface_no_class).
# Control: unique-interface-equality-control (a class implements the
# interface, and two of its objects are compared).
shape := interface<unique>:
    Sides():int

Same(A:shape, B:shape):logic = if (A = B) then true else false

Main():void =
    Print("OVPROBE compiled")

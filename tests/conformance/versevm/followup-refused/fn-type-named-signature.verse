# Book: Tests/Type.versetest:20; Tests/Subtype.versetest:120 (2 cases): a
# function type written with a name for its signature, type{f():void}, as a
# field's type. The Book's tests expect them valid.
# OpenVerse (ce8632ea, Lean) refuses this probe: "a top-level definition must
# start at column 0"
# If UEFN 43.12 admits it, it prints
#   called
# and OpenVerse has a gap on Verse that Epic ships; if it refuses it, the Book
# is ahead of the shipped compiler here and OpenVerse's refusal is Epic's.
holder := class:
    Handler:type{f():void}

Noop():void = Print("OVPROBE called")

Main():void =
    H := holder{Handler := Noop}
    H.Handler()

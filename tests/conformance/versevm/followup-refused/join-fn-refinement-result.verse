# Book: Tests/WhereConstrainedInts.versetest 237, 241 (2 cases): the branches
# of an if, function parameters of types type{_():small} and type{_():int},
# small a refinement of int, at type{_():int} (the Book's cases use i64). The
# Book's tests expect them valid.
# OpenVerse (ce8632ea, Lean) refuses this probe: "the branches have different
# types: type{_():small} and type{_():int}"
# If UEFN 43.12 admits it, it prints
#   value 1
# and OpenVerse has a gap on Verse that Epic ships; if it refuses it, the Book
# is ahead of the shipped compiler here and OpenVerse's refusal is Epic's.
small := type{_X:int where 0 <= _X, _X <= 100}

One():small = 1
Two():int = 2

Pick(G:type{_():small}, H:type{_():int}, Z:logic):type{_():int} = if (Z?) then G else H

Main():void =
    F := Pick(One, Two, true)
    Print("OVPROBE value {F()}")

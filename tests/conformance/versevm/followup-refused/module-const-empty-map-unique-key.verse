# Book: Tests/Map.versetest:decls (1 case): a module constant that is an empty
# map keyed by a class<unique>, [c0]int = map{} (no object in it). The Book's
# tests expect it valid.
# OpenVerse (ce8632ea, Lean) refuses this probe: "the constant Empty would
# hold an object with var fields or of a <unique> class, which would be a new
# one at each use: make it a function"
# If UEFN 43.12 admits it, it prints
#   length 0
# and OpenVerse has a gap on Verse that Epic ships; if it refuses it, the Book
# is ahead of the shipped compiler here and OpenVerse's refusal is Epic's.
c0 := class<unique>{}

Empty:[c0]int = map{}

Main():void =
    Print("OVPROBE length {Empty.Length}")

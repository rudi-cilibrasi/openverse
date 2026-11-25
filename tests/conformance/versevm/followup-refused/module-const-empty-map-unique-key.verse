# Book: Tests/Map.versetest:decls (1 case): a module constant that is an empty
# map keyed by a class<unique>, [c0]int = map{} (no object in it). The Book's
# tests expect it valid.
# OpenVerse (ce8632ea, Lean) refused this probe: "the constant Empty would
# hold an object with var fields or of a <unique> class, which would be a new
# one at each use: make it a function"
# Epic's Verse VM (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086,
# 2026-11-20) admitted it and printed
#   length 0
# OpenVerse now prints it too (#724, Lean and C): a module constant that is an
# empty map{}, array{} or false holds no object, whatever its type
# (tests/verse/module_const_unique).
c0 := class<unique>{}

Empty:[c0]int = map{}

Main():void =
    Print("OVPROBE length {Empty.Length}")

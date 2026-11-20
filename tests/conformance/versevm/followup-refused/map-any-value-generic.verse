# Book: Tests/Any.versetest:60 (1 case): an [int]string map given for a [t]any
# parameter, t:subtype(comparable). The Book's tests expect it valid.
# OpenVerse (ce8632ea, Lean) refuses this probe: "expected [t]any, found
# [int]string (in a call of MapCount)"
# If UEFN 43.12 admits it, it prints
#   count 2
# and OpenVerse has a gap on Verse that Epic ships; if it refuses it, the Book
# is ahead of the shipped compiler here and OpenVerse's refusal is Epic's.
MapCount(M:[t]any where t:subtype(comparable)):int = M.Length

Main():void =
    M:[int]string = map{0 => "0", 1 => "1"}
    Print("OVPROBE count {MapCount(M)}")

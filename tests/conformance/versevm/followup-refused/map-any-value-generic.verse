# Book: Tests/Any.versetest:60 (1 case): an [int]string map given for a [t]any
# parameter, t:subtype(comparable). The Book's tests expect it valid.
# OpenVerse (ce8632ea, Lean) refused this probe: "expected [t]any, found
# [int]string (in a call of MapCount)"
# Epic's Verse VM (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086,
# 2026-11-20) admitted it and printed
#   count 2
# OpenVerse now prints it too (#724, Lean and C): an any inside a generic
# parameter's type takes any type and binds nothing
# (tests/verse/generic_any_inside).
MapCount(M:[t]any where t:subtype(comparable)):int = M.Length

Main():void =
    M:[int]string = map{0 => "0", 1 => "1"}
    Print("OVPROBE count {MapCount(M)}")

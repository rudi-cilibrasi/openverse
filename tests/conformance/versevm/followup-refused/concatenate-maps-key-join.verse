# Book: Tests/Intrinsics/ConcatenateMaps.versetest:67 (1 case):
# ConcatenateMaps of an [int]string and a [string]string map, keys joined at
# comparable. The Book's tests expect it valid.
# OpenVerse (ce8632ea, Lean) refused this probe: "expected int, found string"
# Epic's Verse VM (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086,
# 2026-11-20) admitted it and printed
#   length 2
# OpenVerse now prints it too (#724, Lean and C): ConcatenateMaps of maps
# keyed by different types gives a map keyed by their join, here comparable
# (tests/verse/concatenate_maps_key_join).
Main():void =
    M := ConcatenateMaps(map{0 => "zero"}, map{"0" => "string zero"})
    Print("OVPROBE length {M.Length}")

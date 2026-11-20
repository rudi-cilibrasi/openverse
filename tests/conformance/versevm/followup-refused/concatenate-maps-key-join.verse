# Book: Tests/Intrinsics/ConcatenateMaps.versetest:67 (1 case):
# ConcatenateMaps of an [int]string and a [string]string map, keys joined at
# comparable. The Book's tests expect it valid.
# OpenVerse (ce8632ea, Lean) refuses this probe: "expected int, found string"
# If UEFN 43.12 admits it, it prints
#   length 2
# and OpenVerse has a gap on Verse that Epic ships; if it refuses it, the Book
# is ahead of the shipped compiler here and OpenVerse's refusal is Epic's.
Main():void =
    M := ConcatenateMaps(map{0 => "zero"}, map{"0" => "string zero"})
    Print("OVPROBE length {M.Length}")

# Book: Tests/GetSecondsSinceEpoch.versetest 6, 12, 16 (3 cases):
# GetSecondsSinceEpoch() of /Verse.org/Verse (the Book's API reference:
# <public>, <reads>, a float). The Book's tests expect them valid.
# OpenVerse (ce8632ea, Lean) refuses this probe: "unknown function
# 'GetSecondsSinceEpoch'"
# If UEFN 43.12 admits it, it prints
#   after 2001
# and OpenVerse has a gap on Verse that Epic ships; if it refuses it, the Book
# is ahead of the shipped compiler here and OpenVerse's refusal is Epic's.
Main():void =
    T := GetSecondsSinceEpoch()
    if (T > 1000000000.0):
        Print("OVPROBE after 2001")

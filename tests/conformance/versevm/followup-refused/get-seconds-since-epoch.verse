# Book: Tests/GetSecondsSinceEpoch.versetest 6, 12, 16 (3 cases):
# GetSecondsSinceEpoch() of /Verse.org/Verse (the Book's API reference:
# <public>, <reads>, a float). The Book's tests expect them valid.
# OpenVerse (ce8632ea, Lean) refused this probe: "unknown function
# 'GetSecondsSinceEpoch'"
# Epic's Verse VM (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086,
# 2026-11-20) admitted it and printed
#   after 2001
# OpenVerse now prints it too (#724, Lean and C): its clock is frozen at
# 1795132800.0 (2026-11-20T00:00:00Z), a documented difference from Epic's
# wall clock (docs/LANGUAGE.md, "Random numbers, the clock and the player
# map"; tests/verse/get_seconds_since_epoch).
Main():void =
    T := GetSecondsSinceEpoch()
    if (T > 1000000000.0):
        Print("OVPROBE after 2001")

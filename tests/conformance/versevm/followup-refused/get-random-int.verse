# Book: Tests/Bugs/FORT-995029-CrashHashingDynamicallyTypedMapKey.versetest
# 10, 18 (2 cases): GetRandomInt of /Verse.org/Random, with a using of the
# module. The Book's tests expect them valid.
# OpenVerse (ce8632ea, Lean) refused this probe: "unknown function
# 'GetRandomInt'"
# Epic's Verse VM (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086,
# 2026-11-20) admitted it and printed
#   random 3
# OpenVerse now prints it too (#724, Lean and C): GetRandomInt draws from a
# generator with a fixed seed, a documented difference from Epic's entropy
# (docs/LANGUAGE.md, "Random numbers, the clock and the player map";
# tests/verse/get_random_int).
using { /Verse.org/Random }

Main():void =
    Print("OVPROBE random {GetRandomInt(3, 3)}")

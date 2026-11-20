# Book: Tests/Bugs/FORT-995029-CrashHashingDynamicallyTypedMapKey.versetest
# 10, 18 (2 cases): GetRandomInt of /Verse.org/Random, with a using of the
# module. The Book's tests expect them valid.
# OpenVerse (ce8632ea, Lean) refuses this probe: "unknown function
# 'GetRandomInt'"
# If UEFN 43.12 admits it, it prints
#   random 3
# and OpenVerse has a gap on Verse that Epic ships; if it refuses it, the Book
# is ahead of the shipped compiler here and OpenVerse's refusal is Epic's.
using { /Verse.org/Random }

Main():void =
    Print("OVPROBE random {GetRandomInt(3, 3)}")

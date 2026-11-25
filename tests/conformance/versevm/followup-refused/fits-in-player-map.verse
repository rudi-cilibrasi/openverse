# Book: Tests/weak_map.versetest 605, 611, 615 (3 cases): FitsInPlayerMap[X]
# of an int (the Book's API reference: FitsInPlayerMap(Value:t where
# t:subtype(persistable))<reads><decides>:t). The Book's tests expect them
# valid.
# OpenVerse (ce8632ea, Lean) refused this probe: "unknown function
# 'FitsInPlayerMap'"
# Epic's Verse VM (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086,
# 2026-11-20) admitted it and printed
#   fits 5
# OpenVerse now prints it too (#724, Lean and C): FitsInPlayerMap gives a
# value of a type that persists and always succeeds (docs/LANGUAGE.md,
# "Random numbers, the clock and the player map";
# tests/verse/fits_in_player_map).
Main():void =
    X:int = 5
    if (Y := FitsInPlayerMap[X]):
        Print("OVPROBE fits {Y}")

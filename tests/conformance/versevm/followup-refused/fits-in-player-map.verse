# Book: Tests/weak_map.versetest 605, 611, 615 (3 cases): FitsInPlayerMap[X]
# of an int (the Book's API reference: FitsInPlayerMap(Value:t where
# t:subtype(persistable))<reads><decides>:t). The Book's tests expect them
# valid.
# OpenVerse (ce8632ea, Lean) refuses this probe: "unknown function
# 'FitsInPlayerMap'"
# If UEFN 43.12 admits it, it prints
#   fits 5
# and OpenVerse has a gap on Verse that Epic ships; if it refuses it, the Book
# is ahead of the shipped compiler here and OpenVerse's refusal is Epic's.
Main():void =
    X:int = 5
    if (Y := FitsInPlayerMap[X]):
        Print("OVPROBE fits {Y}")

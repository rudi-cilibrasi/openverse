# Book: Tests/persistable.versetest:3 (1 case): a class<final><persistable>
# with a field, constructed. The Book's tests expect it valid.
# OpenVerse (ce8632ea, Lean) refuses this probe: "<persistable> classes are
# not supported yet (#11)"
# If UEFN 43.12 admits it, it prints
#   score 3
# and OpenVerse has a gap on Verse that Epic ships; if it refuses it, the Book
# is ahead of the shipped compiler here and OpenVerse's refusal is Epic's.
saved := class<final><persistable>:
    Score:int = 0

Main():void =
    S := saved{Score := 3}
    Print("OVPROBE score {S.Score}")

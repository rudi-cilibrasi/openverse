# Book: Tests/Castable.versetest 609, 612, 618 (3 cases):
# castable_subtype(any), an array of it holding a <castable> class. The Book's
# tests expect them valid.
# OpenVerse (ce8632ea, Lean) refuses this probe: "castable_subtype(any):
# openverse writes castable_subtype of a class or an interface only, not of
# any (types as values: docs/research/types-as-values.md)"
# If UEFN 43.12 admits it, it prints
#   length 1
# and OpenVerse has a gap on Verse that Epic ships; if it refuses it, the Book
# is ahead of the shipped compiler here and OpenVerse's refusal is Epic's.
class1 := class<castable>{}

Main():void =
    Types:[]castable_subtype(any) = array{class1}
    Print("OVPROBE length {Types.Length}")

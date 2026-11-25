# Book: Tests/MetatypeConcreteSubtype.versetest 153, 162 (2 cases): a
# <concrete> class bound to a local and constructed through it,
# ClassValue{Value := 7} (the Book's local is Type). The Book's tests expect
# them valid.
# OpenVerse (ce8632ea, Lean) refuses this probe: "unknown struct 'ClassValue'"
# If UEFN 43.12 admits it, it prints
#   value 7
# and OpenVerse has a gap on Verse that Epic ships; if it refuses it, the Book
# is ahead of the shipped compiler here and OpenVerse's refusal is Epic's.
concrete_class := class<concrete>:
    Value:int = 42

Main():void =
    ClassValue := concrete_class
    X := ClassValue{Value := 7}
    Print("OVPROBE value {X.Value}")

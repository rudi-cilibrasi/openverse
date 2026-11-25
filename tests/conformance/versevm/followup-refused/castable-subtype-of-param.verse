# Book: Tests/Castable.versetest 654, 262;
# Tests/ParametricFunctions.versetest:583;
# Tests/Bugs/SOL-8302-CastableSubtypeFailsWithInterfaces.versetest:1 (4
# cases): castable_subtype of a type parameter, X:castable_subtype(t) = t
# inside F(t:castable_subtype(class1)) (the Book's cases also take
# castable_subtype of a parametric class and of a where-variable). The Book's
# tests expect them valid.
# OpenVerse (ce8632ea, Lean) refuses this probe: "castable_subtype(t):
# openverse writes castable_subtype of a class or an interface only, not of t
# (types as values: docs/research/types-as-values.md)"
# If UEFN 43.12 admits it, it prints
#   bound
# and OpenVerse has a gap on Verse that Epic ships; if it refuses it, the Book
# is ahead of the shipped compiler here and OpenVerse's refusal is Epic's.
class1 := class{}
class2 := class<castable>(class1){}

F(t:castable_subtype(class1)):void =
    X:castable_subtype(t) = t
    Print("OVPROBE bound")

Main():void =
    F(class2)

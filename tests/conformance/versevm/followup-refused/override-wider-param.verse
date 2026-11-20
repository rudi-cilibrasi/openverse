# Book: Tests/Overloading.versetest:128; Tests/Super.versetest:56 (2 cases):
# an override whose parameter is a superclass of the overridden method's (a
# contravariant parameter). The Book's tests expect them valid.
# OpenVerse (ce8632ea, Lean) refuses this probe: "derived.F must have the
# signature of base.F, which it overrides"
# If UEFN 43.12 admits it, it prints
#   value 2
# and OpenVerse has a gap on Verse that Epic ships; if it refuses it, the Book
# is ahead of the shipped compiler here and OpenVerse's refusal is Epic's.
animal := class{}
dog := class(animal){}

base := class:
    F(D:dog):int = 1

derived := class(base):
    F<override>(A:animal):int = 2

Main():void =
    B:base = derived{}
    Print("OVPROBE value {B.F(dog{})}")

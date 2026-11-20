# Book: Tests/Subtype.versetest 298, 306, 311, 327, 330, 334, decls (7 cases):
# a parameter of type castable_concrete_subtype(class1), given a
# <castable><concrete> subclass. The Book's tests expect them valid.
# OpenVerse (ce8632ea, Lean) refuses this probe: "unknown parametric type
# 'castable_concrete_subtype' (only structs can be parametric)"
# If UEFN 43.12 admits it, it prints
#   called
# and OpenVerse has a gap on Verse that Epic ships; if it refuses it, the Book
# is ahead of the shipped compiler here and OpenVerse's refusal is Epic's.
class1 := class{}
class2 := class<castable><concrete>(class1){}

F(t:castable_concrete_subtype(class1)):void = Print("OVPROBE called")

Main():void =
    F(class2)

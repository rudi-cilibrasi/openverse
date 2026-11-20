# Book: Tests/MetatypeConcreteSubtype.versetest:49;
# Tests/Attributes/concrete.versetest:245; Tests/Castable.versetest 680, 698
# (4 cases): concrete_subtype(class1) as the bound of a type parameter, F(X:t
# where t:concrete_subtype(class1)). The Book's tests expect them valid.
# OpenVerse (ce8632ea, Lean) refuses this probe: "t:concrete_subtype(…) is not
# supported as a type parameter's bound: a concrete class's subclasses need
# not be concrete, so it is no subtype relation; write t:subtype(…)"
# If UEFN 43.12 admits it, it prints
#   called
# and OpenVerse has a gap on Verse that Epic ships; if it refuses it, the Book
# is ahead of the shipped compiler here and OpenVerse's refusal is Epic's.
class1 := class{}
class2 := class<concrete>(class1){}

F(X:t where t:concrete_subtype(class1)):void = Print("OVPROBE called")

Main():void =
    F(class2{})

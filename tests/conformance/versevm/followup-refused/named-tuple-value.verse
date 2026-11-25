# Book: Tests/Bugs/FORT-590869-NamedWithDefaultCoercion.versetest 9, 19, 26 (3
# cases, verse_vm_todo): a tuple value with a named element, (2, ?Y := 3),
# given as the arguments of a function with a named parameter (the Book's
# cases pass it through a generic Apply). The Book's tests expect them valid.
# OpenVerse (ce8632ea, Lean) refuses this probe: "a tuple with a named element
# (?Name := …) is not supported: the pinned Book of Verse does not settle such
# values, and named parameters inside a tuple parameter are not implemented"
# If UEFN 43.12 admits it, it prints
#   value 5
# and OpenVerse has a gap on Verse that Epic ships; if it refuses it, the Book
# is ahead of the shipped compiler here and OpenVerse's refusal is Epic's.
G(X:int, ?Y:int = 1):int = X + Y

Main():void =
    Print("OVPROBE value {G((2, ?Y := 3))}")

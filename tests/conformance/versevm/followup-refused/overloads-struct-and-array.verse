# Book: Tests/Overloading.versetest:260 (1 case): overloads F(:a) and F(:[]a)
# of an empty struct a. The Book's tests expect it valid.
# OpenVerse (ce8632ea, Lean) refuses this probe: "F is defined twice with
# parameters a call cannot tell apart, (a) and ([]a): overloads must take
# disjoint types"
# If UEFN 43.12 admits it, it prints
#   one 1 many 2
# and OpenVerse has a gap on Verse that Epic ships; if it refuses it, the Book
# is ahead of the shipped compiler here and OpenVerse's refusal is Epic's.
a := struct{}

F(X:a):int = 1
F(X:[]a):int = 2

Main():void =
    Print("OVPROBE one {F(a{})} many {F(array{a{}})}")

# Book: Tests/Overloading.versetest:260 (1 case): overloads F(:a) and F(:[]a)
# of an empty struct a. The Book's tests expect it valid.
# OpenVerse (ce8632ea, Lean) refused this probe: "F is defined twice with
# parameters a call cannot tell apart, (a) and ([]a): overloads must take
# disjoint types"
# Epic's Verse VM (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086,
# 2026-11-20) admitted it and printed
#   one 1 many 2
# OpenVerse now prints it too (#724, Lean and C): one argument is no tuple of
# the arguments, so F(:a) and F(:[]a) are distinct; F(:a, :a) beside F(:[]a)
# is still refused, as the Book has it, 3532
# (tests/verse/overload_scalar_array).
a := struct{}

F(X:a):int = 1
F(X:[]a):int = 2

Main():void =
    Print("OVPROBE one {F(a{})} many {F(array{a{}})}")

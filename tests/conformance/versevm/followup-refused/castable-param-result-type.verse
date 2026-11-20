# Book: Tests/Bugs/BPVMOnly/RefinedMapKeyInterfaceOverride.versetest 117, 121,
# decls (3 cases): a function's castable_subtype parameter Y used as a type in
# its own result, []Y, and as a cast Y[X] (the Book's cases are in
# Tests/Bugs/BPVMOnly/, untagged). The Book's tests expect them valid.
# OpenVerse (ce8632ea, Lean) refuses this probe: "unknown function 'Y'"
# If UEFN 43.12 admits it, it prints
#   found 1
# and OpenVerse has a gap on Verse that Epic ships; if it refuses it, the Book
# is ahead of the shipped compiler here and OpenVerse's refusal is Epic's.
class1 := class{}
class2 := class<castable><unique>(class1){}

F(X:class1, Y:castable_subtype(class1)):[]Y =
    if (Z := Y[X]):
        array{Z}
    else:
        array{}

Main():void =
    Print("OVPROBE found {F(class2{}, class2).Length}")

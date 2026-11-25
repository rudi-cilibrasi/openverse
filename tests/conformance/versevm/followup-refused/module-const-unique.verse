# Book: Tests/GlobalVariables.versetest 72, 73, 74, decls (4 cases): module
# constants that hold objects of a class<unique><allocates><computes>,
# compared (the Book's class is <unique><allocates>; <computes> keeps the
# construction within what a module constant may do, as
# followup-3582/div-const-computes-archetype). The Book's tests expect them
# valid.
# OpenVerse (ce8632ea, Lean) refused this probe: "the constant Instance1 would
# hold an object with var fields or of a <unique> class, which would be a new
# one at each use: make it a function"
# Epic's Verse VM (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086,
# 2026-11-20) admitted it and printed
#   same and different
# OpenVerse now prints it too (#724, Lean and C): a module constant N:c = c{}
# of a <unique> class without fields is one object, the same at every use
# (tests/verse/module_const_unique); other constants that would hold a
# <unique> or var object are still refused.
# Control: module-const-unique-control (the objects made in Main, not in
# module constants).
unique_allocates_class := class<unique><allocates><computes>{}

Instance1:unique_allocates_class = unique_allocates_class{}
Instance2:unique_allocates_class = unique_allocates_class{}

Main():void =
    if (Instance1 = Instance1, Instance1 <> Instance2):
        Print("OVPROBE same and different")

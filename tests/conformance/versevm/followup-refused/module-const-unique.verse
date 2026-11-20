# Book: Tests/GlobalVariables.versetest 72, 73, 74, decls (4 cases): module
# constants that hold objects of a class<unique><allocates><computes>,
# compared (the Book's class is <unique><allocates>; <computes> keeps the
# construction within what a module constant may do, as
# followup-3582/div-const-computes-archetype). The Book's tests expect them
# valid.
# OpenVerse (ce8632ea, Lean) refuses this probe: "the constant Instance1 would
# hold an object with var fields or of a <unique> class, which would be a new
# one at each use: make it a function"
# If UEFN 43.12 admits it, it prints
#   same and different
# and OpenVerse has a gap on Verse that Epic ships; if it refuses it, the Book
# is ahead of the shipped compiler here and OpenVerse's refusal is Epic's.
# Control: module-const-unique-control (the objects made in Main, not in
# module constants).
unique_allocates_class := class<unique><allocates><computes>{}

Instance1:unique_allocates_class = unique_allocates_class{}
Instance2:unique_allocates_class = unique_allocates_class{}

Main():void =
    if (Instance1 = Instance1, Instance1 <> Instance2):
        Print("OVPROBE same and different")

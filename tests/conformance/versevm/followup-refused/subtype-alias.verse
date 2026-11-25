# Book: Tests/TypeAlias.versetest 64, 65 (2 cases): an alias of subtype(c0) as
# a parameter's type, given the class c0. The Book's tests expect them valid.
# OpenVerse (ce8632ea, Lean) refuses this probe: "unknown type 'class_of_c0'
# (supported: int, logic, char, string, void, []t, ?t, tuple(…), and structs
# and enums)"
# If UEFN 43.12 admits it, it prints
#   called
# and OpenVerse has a gap on Verse that Epic ships; if it refuses it, the Book
# is ahead of the shipped compiler here and OpenVerse's refusal is Epic's.
c0 := class{}
class_of_c0 := subtype(c0)

F(C:class_of_c0):void = Print("OVPROBE called")

Main():void =
    F(c0)

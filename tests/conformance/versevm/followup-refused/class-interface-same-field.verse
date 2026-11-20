# Book: Tests/InterfaceWithFields.versetest 247, 260 (2 cases): a class that
# takes a field of one name from a class and from an interface, read through
# each qualifier. The Book's tests expect them valid.
# OpenVerse (ce8632ea, Lean) refuses this probe: "X.(c_a:)Value: both has the
# field Value of c_a and the one of i_b: openverse keeps one field of a name
# in a class, so it cannot tell them apart"
# If UEFN 43.12 admits it, it prints
#   class 12 interface 24
# and OpenVerse has a gap on Verse that Epic ships; if it refuses it, the Book
# is ahead of the shipped compiler here and OpenVerse's refusal is Epic's.
i_b := interface:
    Value:int = 24

c_a := class:
    Value:int = 12

both := class(c_a, i_b){}

Main():void =
    O := both{}
    Print("OVPROBE class {O.(c_a:)Value} interface {O.(i_b:)Value}")

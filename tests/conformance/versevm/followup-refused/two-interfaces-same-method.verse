# Book: Tests/InterfaceWithFields.versetest 86, 238, 463 (3 cases): a class
# that takes the default methods of one name of two interfaces, called through
# each interface's qualifier. The Book's tests expect them valid.
# OpenVerse (ce8632ea, Lean) refuses this probe: "both inherits Method from
# both i_a and i_b: override it in both"
# If UEFN 43.12 admits it, it prints
#   a 12 b 21
# and OpenVerse has a gap on Verse that Epic ships; if it refuses it, the Book
# is ahead of the shipped compiler here and OpenVerse's refusal is Epic's.
i_a := interface:
    Method(X:int):int = X + 10

i_b := interface:
    Method(X:int):int = X + 20

both := class(i_a, i_b){}

Main():void =
    O := both{}
    Print("OVPROBE a {O.(i_a:)Method(2)} b {O.(i_b:)Method(1)}")

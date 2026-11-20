# Book: Tests/Map.versetest:143; Tests/Intrinsics/ConcatenateMaps.versetest:44
# (2 cases): a map literal whose keys are objects of two sibling classes, its
# key type their <unique> base (also through ConcatenateMaps). The Book's
# tests expect them valid.
# OpenVerse (ce8632ea, Lean) refuses this probe: "expected child_a, found
# child_b"
# If UEFN 43.12 admits it, it prints
#   looked up
# and OpenVerse has a gap on Verse that Epic ships; if it refuses it, the Book
# is ahead of the shipped compiler here and OpenVerse's refusal is Epic's.
base := class<unique>{}
child_a := class(base){}
child_b := class(base){}

Main():void =
    A := child_a{}
    B := child_b{}
    M := map{A => 1, B => 2}
    if (M[A] = 1, M[B] = 2):
        Print("OVPROBE looked up")

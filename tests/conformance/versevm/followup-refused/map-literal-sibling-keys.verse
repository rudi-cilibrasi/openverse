# Book: Tests/Map.versetest:143; Tests/Intrinsics/ConcatenateMaps.versetest:44
# (2 cases): a map literal whose keys are objects of two sibling classes, its
# key type their <unique> base (also through ConcatenateMaps). The Book's
# tests expect them valid.
# OpenVerse (ce8632ea, Lean) refused this probe: "expected child_a, found
# child_b"
# Epic's Verse VM (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086,
# 2026-11-20) admitted it and printed
#   looked up
# OpenVerse now prints it too (#724, Lean and C): with no key type expected, a
# map literal's key type is the join of its keys' types, here the <unique>
# base of the two classes (tests/verse/map_key_join).
base := class<unique>{}
child_a := class(base){}
child_b := class(base){}

Main():void =
    A := child_a{}
    B := child_b{}
    M := map{A => 1, B => 2}
    if (M[A] = 1, M[B] = 2):
        Print("OVPROBE looked up")

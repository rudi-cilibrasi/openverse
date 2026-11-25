# Book: Tests/WhereConstrainedInts.versetest 179, decls;
# Tests/WhereConstrainedFloats.versetest 59, decls (4 cases): two overloads of
# F on disjoint refinements of int, called with a literal in each. The Book's
# tests expect them valid.
# OpenVerse (ce8632ea, Lean) refused this probe: "F is defined twice with
# parameters a call cannot tell apart, (small) and (negative): overloads must
# take disjoint types"
# Epic's Verse VM (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086,
# 2026-11-20) admitted it and printed
#   negative 0 small 1
# OpenVerse now prints it too (#724, Lean and C): refinements of one base
# whose intervals have no number in common are disjoint overload domains, and
# a call takes the one its argument's type or literal is of
# (tests/verse/overload_refinements).
# Control: refinement-overloads-control (one F, on one refinement).
small := type{_X:int where 0 <= _X, _X < 65535}
negative := type{_X:int where _X < 0}

F(X:small):int = X
F(X:negative):int = X + 1

Main():void =
    Print("OVPROBE negative {F(-1)} small {F(1)}")

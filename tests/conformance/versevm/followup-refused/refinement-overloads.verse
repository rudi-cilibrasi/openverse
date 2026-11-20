# Book: Tests/WhereConstrainedInts.versetest 179, decls;
# Tests/WhereConstrainedFloats.versetest 59, decls (4 cases): two overloads of
# F on disjoint refinements of int, called with a literal in each. The Book's
# tests expect them valid.
# OpenVerse (ce8632ea, Lean) refuses this probe: "F is defined twice with
# parameters a call cannot tell apart, (small) and (negative): overloads must
# take disjoint types"
# If UEFN 43.12 admits it, it prints
#   negative 0 small 1
# and OpenVerse has a gap on Verse that Epic ships; if it refuses it, the Book
# is ahead of the shipped compiler here and OpenVerse's refusal is Epic's.
# Control: refinement-overloads-control (one F, on one refinement).
small := type{_X:int where 0 <= _X, _X < 65535}
negative := type{_X:int where _X < 0}

F(X:small):int = X
F(X:negative):int = X + 1

Main():void =
    Print("OVPROBE negative {F(-1)} small {F(1)}")

# Book: Tests/WhereConstrainedInts.versetest:203;
# Tests/WhereConstrainedFloats.versetest:114 (2 cases): the negation of a
# local bound to a literal, UChar := 200, given where a refinement that holds
# -200 is expected, without a cast (a local keeps its literal's type). The
# Book's tests expect them valid.
# OpenVerse (ce8632ea, Lean) refuses this probe: "an int is a negative_uchar
# only after a cast: write negative_uchar[X], which fails when X is not one"
# If UEFN 43.12 admits it, it prints
#   negated -200
# and OpenVerse has a gap on Verse that Epic ships; if it refuses it, the Book
# is ahead of the shipped compiler here and OpenVerse's refusal is Epic's.
negative_uchar := type{_X:int where _X <= 0, -256 < _X}

Main():void =
    UChar := 200
    N:negative_uchar = -UChar
    Print("OVPROBE negated {N}")

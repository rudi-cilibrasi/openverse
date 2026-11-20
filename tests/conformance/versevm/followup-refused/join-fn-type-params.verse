# Book: Tests/ParametricTypes.versetest 1321, 1329 (2 cases): the branches of
# an if, function parameters of types type{_(:t):void} and type{_(:u):void},
# u:subtype(t), at type{_(:u):void}; compile only, as the Book's cases (a call
# would meet UEFN 43.12's 3502 for a generic function whose result has a
# function of its type parameter, followup-coerce/generic-result-fn). The
# Book's tests expect them valid.
# OpenVerse (ce8632ea, Lean) refuses this probe: "the branches have different
# types: type{_(:t):void} and type{_(:u):void}"
# If UEFN 43.12 admits it, it prints
#   compiled
# and OpenVerse has a gap on Verse that Epic ships; if it refuses it, the Book
# is ahead of the shipped compiler here and OpenVerse's refusal is Epic's.
Pick(X:int, t:type, u:subtype(t), Y(:t):void, Z(:u):void):type{_(:u):void} =
    if (X = 1):
        Y
    else:
        Z

Main():void =
    Print("OVPROBE compiled")

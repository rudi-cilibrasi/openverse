# A type given as an argument of a call in brackets, a <decides>
# function's, as one in parentheses: First[string, Xs] (Book of Verse
# ch. 11, types as values; the tests' FalseOption(int),
# ParametricTypes.versetest 613-624).
First(t:type, Xs:[]t)<decides>:t = Xs[0]
Pick(t:type, Xs:[]t, I:int)<decides>:t =
    I >= 0
    Xs[I]
Main():void =
    Xs:[]string = array{"a", "b"}
    if (S := First[string, Xs], T := Pick[string, Xs, 1]) then Print("{S}{T}")
    if (not First[int, array{}]) then Print("empty")
    if (not Pick[int, array{1}, -1]) then Print("negative")

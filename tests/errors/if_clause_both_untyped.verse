# expect: if_clause_both_untyped.verse:6:33: the type of an empty array{} must be given
# An if with an index as its first clause takes the type any if takes
# (ifBranches): with neither branch typed alone, the then's error, as with
# the index alone or later, not the else's alone first (#583)
F(Xs:[]int, K:int):void =
    if (X := Xs[1], K > -5) then array{} else array{}
    Print("{K}")
Main():void =
    F(array{1}, 1)

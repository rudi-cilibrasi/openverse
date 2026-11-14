# An if with an index as its first clause takes the type any if takes
# (ifBranches): its branches, two empty array{}s with no type from their
# context, are arrays of false (Book of Verse tests, Array.versetest:90), so
# the if is one (#583).
F(Xs:[]int, K:int):void =
    if (X := Xs[1], K > -5) then array{} else array{}
    Print("{K}")
Main():void =
    F(array{1}, 1)

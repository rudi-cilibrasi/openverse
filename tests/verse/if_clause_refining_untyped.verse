# An if whose cast refines type arguments, with clauses after it (#286): the
# if's type is any if's (ifBranches), its branch typed under the refinement,
# an empty array{} with no type from its context an array of false (Book of
# Verse tests, Array.versetest:90).
box(t:type) := class:
    V:t
ibox := class(box(int)):
    W:int = 2
F(B:box(t) where t:type):void =
    var N:int = 0
    if (I := ibox[B], I.W > 0) then array{} else 1
    Print("{N}")
Main():void =
    F(ibox{V := 1})

# expect: if_clause_refining_untyped.verse:11:36: the type of an empty array{} must be given
# An if whose cast refines type arguments, with clauses after it (#286): the
# if's type is any if's (ifBranches), its branch typed under the refinement;
# with none, the branch's own error, not the cast's refusal as a statement
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

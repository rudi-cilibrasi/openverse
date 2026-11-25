# (#759) A `for` whose first clause picks a branch with a choice (an `if`
# whose branches are choices, or a call of a function whose body is one),
# followed by a generator whose source writes. The row V = 3 has no W, so
# it reaches no body and what its source wrote is undone: only the row
# V = 1 adds its 100. The controls write the same rows with forms that
# already followed that rule: a written choice, an array, a choice with the
# `if` inside one alternative, and an index in place of the generator.
Cell := class{var N:int = 0}
C(S:Cell)<transacts><decides>:void =
    S.N >= 0
Inner(S:Cell, V:int)<transacts>:[]int =
    set S.N += 100
    if (V = 1) then array{1} else array{}
Two(S:Cell)<transacts>:int =
    if (C[S]) then (3 | 1) else (4 | 1)
IfCall(S:Cell)<transacts>:void =
    for (V := if (C[S]) then (3 | 1) else (4 | 1), W : Inner(S, V)):
        Print("if-call {V} {W} {S.N}")
Call(S:Cell)<transacts>:void =
    for (V := Two(S), W : Inner(S, V)):
        Print("call {V} {W} {S.N}")
IfPlain(S:Cell)<transacts>:void =
    for (V := if (S.N >= 0) then (3 | 1) else (4 | 1), W : Inner(S, V)):
        Print("if-plain {V} {W} {S.N}")
Else(S:Cell)<transacts>:void =
    for (V := if (S.N < 0) then (4 | 1) else (3 | 1), W : Inner(S, V)):
        Print("else {V} {W} {S.N}")
Choice(S:Cell)<transacts>:void =
    for (V := (3 | 1), W : Inner(S, V)):
        Print("choice {V} {W} {S.N}")
Arr(S:Cell)<transacts>:void =
    for (V : array{3, 1}, W : Inner(S, V)):
        Print("array {V} {W} {S.N}")
Inside(S:Cell)<transacts>:void =
    for (V := (if (C[S]) then 3 else 4) | 1, W : Inner(S, V)):
        Print("inside {V} {W} {S.N}")
Index(S:Cell)<transacts>:void =
    for (V := if (C[S]) then (3 | 1) else (4 | 1), W := Inner(S, V)[0]):
        Print("index {V} {W} {S.N}")
Run(Name:string, F(:Cell)<transacts>:void)<transacts>:void =
    S := Cell{}
    F(S)
    Print("{Name} state {S.N}")
Main()<transacts>:void =
    Run("if-call", IfCall)
    Run("call", Call)
    Run("if-plain", IfPlain)
    Run("else", Else)
    Run("choice", Choice)
    Run("array", Arr)
    Run("inside", Inside)
    Run("index", Index)

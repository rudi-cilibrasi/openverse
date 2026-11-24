# A string's interpolated values are made text where they are written, each
# before the code of the next one runs (interpolation calls ToString, then
# joins the pieces, LANGUAGE.md), also when a later one has a choice or a call
# of a function with several values whose clauses are lifted before the
# string (#723): the text of the first is the same for every value of the
# second, and what the second's code does comes after the first is read.
Tell(S:string, X:int)<transacts>:int =
    Print(S)
    X
Big(X:int)<transacts>:int = 9223372036854775807 + X
Two(X:int)<transacts>:int = X | X + 1
Main():void =
    if (T := "<{Big(0)}-{(if (Print("c1"), 1 = 1) then (2 | 4) else 3)}>", T.Length > 1) then Print(T) else Print("no")
    for (T := "<{Tell("a2", Big(0))}-{Two(Tell("c2", 1))}>") { Print(T) }
    var N:int = 5
    for (T := "<{N}-{(set N += 1; N) | 9}-{Two(Tell("c3", N))}>") { Print(T) }
    for (T := "{1.5}{'x'}{"s"}{Two(3)}") { Print(T) }

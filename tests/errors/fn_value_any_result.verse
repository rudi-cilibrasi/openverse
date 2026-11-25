# expect: is not yet implemented
# A function named where a function type with an any result is expected is
# converted (#724, tests/verse/fn_named_any_result); a function value that
# is not named there is not, as Epic's compiler refuses it (3502).
Succ(X:int):int = X + 1
Call(G(:int):any):any = G(0)
Main():void =
    G := Succ
    Call(G)

# expect: expected type{_(:int):comparable}, found type{_(:int):int}
# A function named at a function type with a comparable result is not
# converted (its int would be boxed); at an any result it is (#724,
# tests/verse/fn_named_any_result).
Succ(X:int):int = X + 1
Call(G(:int):comparable):comparable = G(0)
Main():void =
    Call(Succ)

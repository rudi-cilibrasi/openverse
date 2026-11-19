# expect: the result of Wrap, type{_(:t):void}, has its type parameter t inside a function type
# (#724) a generic function whose result is (t->void), called at int
# (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, error 3502: followup-coerce/generic-result-fn).
TakeInt(X:int):void = Print("took {X}")
Wrap(X:t, F(:t):void where t:type):(t->void) = F
Main():void =
    G := Wrap(1, TakeInt)
    G(5)

# refinement subtyping by interval, and negation flipping a refinement's bounds (#143)
percent := type{_X:float where 0.0 <= _X, _X <= 1.0}
negative_percent := type{_X:float where -1.0 <= _X, _X <= 0.0}
finite := type{_X:float where -Inf < _X, _X < Inf}
small := type{_X:int where 0 <= _X, _X < 10}
digit := type{_X:int where 0 <= _X, _X <= 9}
MakePercent():percent = 0.25
Half(X:finite):float = X / 2.0
D(X:digit):int = X
Main():void =
    NegValue:negative_percent = -MakePercent()
    P:percent = MakePercent()
    Print("{NegValue} {Half(P)}")
    S:small = 7
    Print("{D(S)}")

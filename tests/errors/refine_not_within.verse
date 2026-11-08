# expect: 7:14: expected tiny, found percent
percent := type{_X:float where 0.0 <= _X, _X <= 1.0}
tiny := type{_X:float where 0.0 <= _X, _X < 0.5}
F(X:tiny):float = X
Main():void =
    P:percent = 0.25
    Print("{F(P)}")

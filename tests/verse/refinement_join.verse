# refinements join at an expected refinement holding both (#143 review)
small := type{_X:int where 0 <= _X, _X < 10}
digit := type{_X:int where 0 <= _X, _X <= 9}
neg := type{_X:int where _X < 0}
G(X:digit):int = X
Main():void =
    S:small = 3
    N:neg = -4
    R:digit = if (S > 2) then S else 5
    Print("{G(R)}")

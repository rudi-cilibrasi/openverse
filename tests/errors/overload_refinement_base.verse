# expect: parameters a call cannot tell apart, (small) and (int)
# A refinement overlaps its base (#136); only disjoint refinements are
# distinct overloads (#724, tests/verse/overload_refinements).
small := type{_X:int where 0 <= _X, _X < 65535}
F(X:small):int = X
F(X:int):int = X + 1
Main():void =
    Print("{F(1)}")

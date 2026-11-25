# expect: parameters a call cannot tell apart, (small) and (low)
# Overloads on refinements are distinct only when their intervals have no
# number in common (#724, tests/verse/overload_refinements): 0 is of both.
small := type{_X:int where 0 <= _X, _X < 65535}
low := type{_X:int where _X <= 0}
F(X:small):int = X
F(X:low):int = X + 1
Main():void =
    Print("{F(0)}")

# expect: no overload of F takes (int)
# Overloads on disjoint refinements are chosen by the argument's type, not
# its value at run time (#724, tests/verse/overload_refinements): an int
# that is no literal is of neither without a cast.
small := type{_X:int where 0 <= _X, _X < 65535}
negative := type{_X:int where _X < 0}
F(X:small):int = X
F(X:negative):int = X + 1
Main():void =
    Y:int = 3
    Print("{F(Y)}")

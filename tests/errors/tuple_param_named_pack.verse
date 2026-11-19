# expect: F takes 1 positional argument(s), found 2: several arguments are not packed into a tuple parameter beside a named one
# Two arguments are not packed into a tuple parameter beside a named one
# (#724): the function's parameter is then the tuple of its parameters,
# named ones included. UEFN 43.12 (++Fortnite+Release-43.12-CL-60598086)
# refuses F(1.0, 2.0) with error 3509, "This function parameter expects a
# value of type tuple(tuple(float,float),?E:float = ...), but this argument
# is an incompatible value of type tuple(type{1.000000},type{2.000000})"
# (followup-book2/overload-tuple-named-call; the Book's tests,
# Bugs/FORT-744399-DefaultTupleFieldsCrashComplier.versetest:62).
F(X:tuple(float, float), ?E:float = 0.1):float = X(0) + X(1) + E
Main():void =
    Sum := F(1.0, 2.0)

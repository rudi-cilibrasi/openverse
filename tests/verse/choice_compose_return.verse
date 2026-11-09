# a return in the clauses after a composed choice: they run in the function, so it leaves it (#283)
A():int = 1 | 2
F():int =
    if (X := A() | 9, if (X = 2) then return 42 else true, X > 5) then X else 0
Main():void = Print("{F()}")

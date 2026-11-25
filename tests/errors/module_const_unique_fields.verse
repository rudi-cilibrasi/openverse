# expect: the constant I would hold an object with var fields or of a <unique> class
# A module constant of a <unique> class without fields is one object
# (#724, tests/verse/module_const_unique); of a class with fields it is
# still refused.
u := class<unique><allocates><computes>{ N:int = 1 }
I:u = u{}
Main():void =
    Print("{I.N}")

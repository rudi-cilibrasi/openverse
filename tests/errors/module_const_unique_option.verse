# expect: the constant I would hold an object with var fields or of a <unique> class
# Only a constant whose value is the construction itself is one object
# (#724, tests/verse/module_const_unique): inside an option it would be a
# new one at each use.
u := class<unique><allocates><computes>{}
I:?u = option{u{}}
Main():void =
    if (I?). Print("x")

# expect: the constant J would hold an object with var fields or of a <unique> class
# A constant that is another constant's object is still refused (#724,
# tests/verse/module_const_unique): only the construction itself is admitted.
u := class<unique><allocates><computes>{}
I:u = u{}
J:u = I
Main():void =
    if (I = J). Print("x")

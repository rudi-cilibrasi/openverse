# expect: its class u runs code when constructed
# A module constant's own object is made as the program starts, without
# running code (#724, tests/verse/module_const_unique): a class with a
# block: clause is still refused.
u := class<unique><allocates>:
    block:
        Print("made")
I:u = u{}
Main():void =
    if (I = I). Print("x")

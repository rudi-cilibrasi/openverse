# expect: uses the constant I, which has the effect <allocates>
# A module constant's own object (#724, tests/verse/module_const_unique)
# keeps its construction's effects: a <computes> function cannot use it.
u := class<unique><allocates><computes>{}
I:u = u{}
Pure()<computes>:logic = logic{I = I}
Main():void =
    if (Pure()?). Print("x")

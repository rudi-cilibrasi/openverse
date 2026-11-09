# expect: 4:46: a call of A, which has several values, cannot be lifted from a block with a defer: of its own
A():int = 1 | 2
Main()<transacts>:void =
    for (X := block{ defer: Print("d"); Y := A(); Y }):
        Print("{X}")

# A call with several values in a block with a defer: of its own (#283): the defer: runs as each value leaves the block
A():int = 1 | 2
Main()<transacts>:void =
    for (X := block{ defer: Print("d"); Y := A(); Y }):
        Print("{X}")

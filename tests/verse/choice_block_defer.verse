# A choice in a block with a defer: of its own (#283): the defer: runs as each value leaves the block
Main()<transacts>:void =
    for (X := block{ defer: Print("d"); 1 | 2 }):
        Print("{X}")

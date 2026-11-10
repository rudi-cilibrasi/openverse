# A block with a defer: of its own as an if's branch, with a call with several values (#283): the defer: runs as each value leaves the branch
Two(N : int):int = N | N + 10
Main()<transacts>:void =
    for (X := if (1 = 1) then { defer: Print("d"); Y := Two(1); Y } else 0):
        Print("{X}")

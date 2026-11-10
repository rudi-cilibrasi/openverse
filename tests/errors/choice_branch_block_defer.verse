# expect: 4:59: a call of Two, which has several values, cannot be lifted from here
Two(N : int):int = N | N + 10
Main()<transacts>:void =
    for (X := if (1 = 1) then { defer: Print("d"); Y := Two(1); Y } else 0):
        Print("{X}")

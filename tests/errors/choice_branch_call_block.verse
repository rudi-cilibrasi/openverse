# expect: 4:52: a call of Two, which has several values, cannot be lifted from here
Two(N : int):int = N | N + 10
Main()<transacts>:void =
    for (C := 0..1, X := (if (C = 0) then { Y := Two(1); Y } else 0)):
        Print("{X}")

# expect: 5:32: 'Y' is already defined
Two(N : int):int = N | N + 10
Main()<transacts>:void =
    Y := 5
    for (X := if (Y > 1) then { Y := Two(1); Y } else 0):
        Print("{X}")

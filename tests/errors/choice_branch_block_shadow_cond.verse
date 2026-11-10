# expect: 5:52: 'Y' is already defined
Two(N : int):int = N | N + 10
Main()<transacts>:void =
    M : ?int = option{4}
    for (X : int = if (Y := M?) then { Z := Two(1); Y := Z; Y } else 0):
        Print("{X}")

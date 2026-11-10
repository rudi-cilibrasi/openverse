# expect: 8:18: Od has several values and uses Limit, which is also the name of a member of Self here
Limit:int = 3
Ev(N:int):int = N | Od(N + 1)
Od(N:int):int = if (N > Limit) then -N else Ev(N + 1)
thing := class:
    Limit:int = 10
    Run()<transacts>:void =
        for (X := Ev(0)) { Print("{X}") }
Main()<transacts>:void =
    thing{}.Run()

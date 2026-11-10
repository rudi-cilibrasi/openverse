# expect: 4:46: a call of Down, which has several values, cannot be lifted from here
Down(N : int):int = if (N > 0) then (N | Down(N - 1)) else 0
Main()<transacts>:void =
    for (C := 0..1, X := (if (C = 0) then Down(1))):
        Print("{X}")

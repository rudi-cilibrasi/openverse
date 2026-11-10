# A cycle of three functions with several values, taken lazily (#283; tim-61's
# expectations, written before the code)
A(N:int)<transacts>:int =
    Print("a{N}")
    if (N > 4) then 100 else (N | B(N + 1))
B(N:int)<transacts>:int =
    Print("b{N}")
    if (N > 4) then 200 else C(N + 1)
C(N:int)<transacts>:int =
    Print("c{N}")
    if (N > 4) then 300 else (N * 10 | A(N + 1))
Main()<transacts>:void =
    for (X := A(0)) { Print("x{X}") }

Dup(V:t where t:type):t = V | V
Pick(N:int)<transacts>:int =
    defer: Print("defer int")
    if (N = 1): return N | N + 1
    9 | 10
Pick(S:string)<transacts>:int =
    defer: Print("defer string")
    if (S = "x"): return 20 | 21
    30 | 31
Main()<transacts>:void =
    for (A := Dup(1) | Dup("x"), B := Pick(A)): Print("body {B}")

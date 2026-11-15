Dup(V:t where t:type):t = V | V
Pick(N:int):int = N | N + 1
Pick(S:string):int = 7 | 8
Main()<suspends>:void =
    for (A := Dup(1) | Dup("x"), B := Pick(A)):
        Print("before {B}")
        Sleep(0.0)
        Print("after {B}")

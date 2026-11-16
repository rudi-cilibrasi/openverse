a := class:
    M(N:int)<transacts>:int = N | N + 1
    M(S:string)<transacts>:int = 7 | 8
Dup(V:t where t:type):t = V | V
Main()<transacts>:void =
    for (X := Dup(1), Y := a{}.M(X)) { Print("y {Y}") }
    for (X := Dup("s"), Y := a{}.M(X)) { Print("y {Y}") }

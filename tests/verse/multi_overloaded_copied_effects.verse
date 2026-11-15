box := class:
    var N:int = 0
Default(C:box,Tag:string)<transacts>:int =
    set C.N += 1
    Print("default {Tag} {C.N}")
    C.N
Pick(C:box,N:int,?D:int=Default(C,"int"))<transacts>:int =
    Print("pick int")
    N + D | N + D + 10
Pick(C:box,S:string,?D:int=Default(C,"string"))<transacts>:int =
    Print("pick string {S}")
    100 + D | 110 + D
Dup(V:t where t:type):t = V | V
Main()<transacts>:void =
    C := box{}
    for (A := Dup(1) | Dup("x"), B := Pick(C,A)):
        Print("body {B} {C.N}")
    Print("after for {C.N}")
    F := box{}
    if (A := Dup(1) | Dup("x"), B := Pick(F,A), B = 111):
        Print("first {B} {F.N}")
    Print("after first {F.N}")
    O := box{}
    R := option{A := Dup(1) | Dup("x"); B := Pick(O,A); B = 111; B}
    if (X := R?): Print("option {X} {O.N}")
    Print("after option {O.N}")

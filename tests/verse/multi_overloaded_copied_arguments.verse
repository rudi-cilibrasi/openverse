box := class:
    var N:int = 0
Default(C:box,Tag:string)<transacts>:int =
    set C.N += 1
    Print("{Tag} {C.N}")
    C.N
Arg(C:box)<transacts>:box =
    Print("pos {C.N}")
    C
Pick(C:box,N:int,?D:int=Default(C,"int D"),?E:int=Default(C,"int E"))<transacts>:int =
    Print("pick int")
    N + D + E | N + D + E + 1
Pick(C:box,S:string,?D:int=Default(C,"string D"),?E:int=Default(C,"string E"))<transacts>:int =
    Print("pick string {S}")
    100 + D + E | 101 + D + E
Dup(V:t where t:type):t = V | V
Main()<transacts>:void =
    C := box{}
    for (A := Dup(1) | Dup("x"), B := Pick(Arg(C),A,?E:=Default(C,"given E"))):
        Print("body {B} {C.N}")
    Print("after {C.N}")

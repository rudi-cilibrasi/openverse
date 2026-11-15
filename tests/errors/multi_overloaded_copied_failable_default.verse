# expect: the default of ?D of Pick can fail
# Defaults remain outside failure contexts, including copied overloads.
box := class:
    var N:int = 0
Default(C:box,Tag:string)<transacts><decides>:int =
    set C.N += 1
    Print("default {Tag} {C.N}")
    C.N < 3
    5
Pick(N:int,C:box,?D:int=Default[C,"int"])<transacts><decides>:int = N + D | N + D + 1
Pick(S:string,C:box,?D:int=Default[C,"string"])<transacts><decides>:int = 100 + D | 110 + D
Dup(V:t where t:type):t = V | V
Arg(C:box,Tag:string)<transacts>:box =
    Print("arg {Tag} {C.N}")
    C
Main()<transacts>:void =
    C := box{}
    for (A := Dup(1) | Dup("x"), B := Pick[A,Arg(C,"given")]): Print("body {B} {C.N}")
    Print("after {C.N}")

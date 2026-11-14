# Supplied arguments run as written, followed by omitted defaults in scope.
counter := class:
    var N:int = 0
Tell(H:counter,Label:string,N:int)<transacts>:int =
    set H.N += 1
    Print("{Label} {N} {H.N}")
    N
Order(H:counter,N:int,?A:int=Tell(H,"default A",N*10),?B:int=Tell(H,"default B",A+1))<transacts><decides>:int =
    N <= 1
    Print("visit {N} {A} {B} {H.N}")
    A | Order[H,Tell(H,"pos",N+1),?B:=Tell(H,"named B",N+20)]
Even(H:counter,N:int,?S:int=Tell(H,"even default",1))<transacts><decides>:int =
    N <= 3
    Print("even {N} {S}")
    N | Odd[H,N+S,?S:=Tell(H,"odd arg",S+1)]
Odd(H:counter,N:int,?S:int=Tell(H,"odd default",2))<transacts><decides>:int =
    N <= 3
    Print("odd {N} {S}")
    N | Even[H,N+S]
Arr:[]int = array{10,20}
Maybe(N:int,?V:int=Arr[N])<computes><decides>:int = V | Maybe[N+1]
Pick(N:int,?V:int=Arr[N])<computes><decides>:int = N | V
Eager(N:int,?K:int=2)<computes><decides>:int =
    if (N>0) then (Pick[N,?V:=K] | Pick[N] | Eager[N-1]) else 0
Main()<transacts>:void =
    H := counter{}
    for (X := Order[H,0,?B:=Tell(H,"initial B",7),?A:=Tell(H,"initial A",5)]):
        Print("all {X}")
    Print("state {H.N}")
    if (X := Order[H,0], X > 5) then Print("first {X} {H.N}")
    if (X := Order[H,0], X > 99) then Print("unexpected") else Print("none {H.N}")
    for (X := Even[H,0]): Print("group {X}")
    if (X := Odd[H,0], X > 1) then Print("group first {X}")
    for (X := Maybe[0]): Print("maybe {X}")
    if (X := Maybe[0], X > 10) then Print("maybe first {X}")
    for (X := Eager[2]): Print("eager {X}")

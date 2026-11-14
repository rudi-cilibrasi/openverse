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
Main()<transacts>:void =
    H := counter{}
    for (X := Order[H,0,?B:=Tell(H,"initial B",7),?A:=Tell(H,"initial A",5)]):
        Print("all {X}")
    Print("state {H.N}")
    if (X := Order[H,0], X > 5) then Print("first {X} {H.N}")
    if (X := Order[H,0], X > 99) then Print("unexpected") else Print("none {H.N}")
    for (X := Even[H,0]): Print("group {X}")
    if (X := Odd[H,0], X > 1) then Print("group first {X}")

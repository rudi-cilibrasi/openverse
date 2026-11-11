box := class:
    K:int
    Walk(Other:box,N:int)<transacts><decides>:int =
        var Receiver:box=Self
        if(N>0) then (K+N | Receiver.Walk[(block{set Receiver=Other;Other},N-1)]) else K+N
Main()<transacts>:void =
    P:=box{K:=1}
    Q:=box{K:=9}
    if(V:=P.Walk[Q,1],V=1) then Print("win {V}") else Print("bad missing")
    if(V:=P.Walk[Q,1],V=9) then Print("bad receiver") else Print("none")

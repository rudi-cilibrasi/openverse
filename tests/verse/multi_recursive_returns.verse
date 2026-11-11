Walk(N:int)<transacts>:int =
    Print("enter {N}")
    if(N<=0):
        Print("stop")
        B:=N+10
        return B|B+1
    Print("tail {N}")
    M:=N-1
    N|Walk(M)
Expand(N:int)<computes>:int =
    if(N<=0): return 1|2
    return 10+Expand(N-1)
Main():void =
    for(X:=Walk(2)): Print("got {X}")
    if(X:=Walk(2),X>9)then Print("first {X}")else Print("none")
    if(X:=Walk(2),X>20)then Print("bad")else Print("reject")
    for(X:=Expand(2)): Print("eager {X}")

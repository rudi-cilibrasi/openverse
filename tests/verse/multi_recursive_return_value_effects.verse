# Returning a value block keeps its effects at the value boundary.
R(N:int)<transacts>:int =
    if(N<=0): return (Print("value");1)|2
    N|R(N-1)
Main():void =
    for(X:=R(0),X>2): Print("bad")
    Print("empty")
    if(X:=R(0),X>2)then Print("bad")else Print("none")
    for(X:=R(0),X=1): Print("got {X}")
    if(X:=R(0),X=2)then Print("first {X}")else Print("bad")

# Direct projection in inline, lazy and eager producers, including defaults.
box(t:type) := struct { E:[]t=Concatenate(); V:int }
Many(X:t,N:int where t:type)<computes>:int = box(t){V:=N|N+1}.V
Eager(X:t,N:int where t:type)<computes>:int =
    if(N>0)then (box(t){V:=N|N+1}.V | Eager(X,N-1)) else box(t){V:=0}.V
Lazy(X:t,N:int where t:type)<transacts><decides>:int =
    N>0
    Print("visit {N}")
    box(t){V:=N}.V | Lazy[X,N-1]
bad(t:type) := struct { E:[]t=Concatenate(); D:int=None[]; V:int }
None()<computes><decides>:int =
    false?
    0
Failed(X:t,N:int where t:type)<computes><decides>:int =
    if(N>0)then (bad(t){V:=N|N+1}.V | Failed[X,N-1]) else 0
Main():void =
    for(V:=Many(7,3)): Print("many {V}")
    for(V:=Eager("s",2)): Print("eager {V}")
    if(V:=Lazy["s",3], V<2)then Print("first {V}")
    if(V:=Lazy[7,2], V<0)then Print("unexpected")else Print("none")
    for(V:=Failed[7,2]): Print("failed {V}")

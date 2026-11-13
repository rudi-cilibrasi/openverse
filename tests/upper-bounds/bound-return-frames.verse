# Recursive return frames keep actual bounds in their suffix and prefix.
vehicle:=class<computes>{N:int=7}
car:=class<computes>(vehicle){Name:string="precise"}
Rep(X:t,N:int where t:subtype(vehicle))<transacts><decides>:[]t=
    N>=0
    Empty:[]t=array{}
    R:=Rep[X,N-1]|Empty
    Print("frame {N} {X.N}")
    R+array{X}
Tell(S:string,N:int)<transacts>:int=(Print(S);N)
Prefix(X:t,N:int where t:subtype(vehicle))<transacts><decides>:int=
    N>0
    Tell("before {N} {X.N}",X.N)+Prefix[X,N-1]|X.N
Lazy(X:t,N:int where t:subtype(vehicle))<transacts>:int=
    if(N<=0)then(if(Print("lazy {X.N}"),X.N>5)then X.N else 0)else(N|Lazy(X,N-1))
Main()<transacts>:void=
    A:=car{}
    for(V:=Rep[A,2]):
        if(X:=V[0])then Print("row {V.Length} {X.Name}")
    for(V:=Prefix[A,2]):Print("prefix {V}")
    if(V:=Prefix[A,2],V>14)then Print("bad {V}")else Print("prefix rollback")
    for(V:=Lazy(A,0),V>10):Print("bad {V}")
    Print("lazy rollback")
    for(V:=Lazy(A,2)):Print("value {V}")

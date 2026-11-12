vehicle:=class<computes>{N:int=7}
car:=class<computes>(vehicle){Name:string="precise"}
Frames(X:car,N:int)<transacts><decides>:tuple(int,car)=
    N>0
    var K:int=N*10
    var Saved:car=X
    R:=Frames[X,N-1]|(N,X)
    set Saved=R(1)
    set K+=R(0)
    Print("frame {N} {K} {Saved.N}")
    (K,Saved)
Two(X:car)<computes>:car=X|X
Break(X:car)<transacts>:int=
    var V:int=0
    loop:
        defer:Print("break cleanup {V}")
        if(A:=(Two(X)|Two(X)),B:=(1|2),set V+=A.N+B,B=2,break)then Print("bad")
    V
Main()<transacts>:void=
    A:=car{}
    for(V:=Frames[A,2]):Print("value {V(0)} {V(1).Name}")
    for(V:=Frames[A,2],V(0)>31):Print("rejected {V(0)}")
    if(V:=Frames[A,2],V(0)>31)then Print("bad")else Print("none")
    if(V:=Frames[A,2],V(0)>25)then Print("first {V(0)} {V(1).Name}")
    Print("break {Break(A)}")

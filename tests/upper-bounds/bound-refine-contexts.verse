vehicle:=class<allocates>{var N:int=1}
car:=class<allocates>(vehicle){Name:string="car"}
truck:=class<allocates>(vehicle){Name:string="truck"}
cell:=class<allocates>{var N:int=0}
pair(a:subtype(vehicle),b:subtype(vehicle)):=class<computes>:
    A:a
    B:b
dup(t:subtype(vehicle)):=class<computes>(pair(t,t)){C:int=4}
Read(X:t where t:subtype(vehicle))<reads>:int=X.N
Opt(P:pair(a,b) where a:subtype(vehicle),b:subtype(vehicle))<reads>:?int=option{D:=dup[P];Read(D.B)}
Undo(H:cell,P:pair(a,b),Min:int where a:subtype(vehicle),b:subtype(vehicle))<transacts>:?int=
    option{set H.N+=1;D:=dup[P];set D.B.N+=H.N;Read(D.B)>Min;Read(D.B)}
And(P:pair(a,b),N:int where a:subtype(vehicle),b:subtype(vehicle))<reads>:int=if(N>0 and (D:=dup[P];Read(D.B)>N))then 1 else 0
Or(P:pair(a,b),N:int where a:subtype(vehicle),b:subtype(vehicle))<reads>:int=if((D:=dup[P];Read(D.B)>N) or N<0)then 1 else 0
Not(P:pair(a,b) where a:subtype(vehicle),b:subtype(vehicle))<computes>:int=if(not dup[P])then 1 else 0
Main()<transacts>:void=
    A:=car{N:=7}
    B:=car{N:=9}
    T:=truck{N:=3}
    Y:pair(car,car)=dup(car){A:=A,B:=B}
    Z:pair(car,truck)=pair(car,truck){A:=A,B:=T}
    H:=cell{}
    if(V:=Opt(Y)?)then Print("opt {V}")else Print("bad")
    if(Opt(Z)?)then Print("bad")else Print("opt no")
    if(V:=Undo(H,Y,9)?)then Print("undo {V} {H.N}")else Print("bad")
    if(Undo(H,Y,100)?)then Print("bad")else Print("rollback {B.N} {H.N}")
    if(Undo(H,Z,0)?)then Print("bad")else Print("cast rollback {T.N} {H.N}")
    Print("and {And(Y,9)} {And(Y,10)} {And(Z,1)}")
    Print("or {Or(Y,9)} {Or(Y,10)} {Or(Z,-1)} {Or(Z,1)}")
    Print("not {Not(Y)} {Not(Z)}")

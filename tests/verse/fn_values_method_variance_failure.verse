cell:=class{var N:int=0}
box(t:subtype(comparable)):=class:
    V:t
    C:cell
    Match(X:t)<transacts><decides>:tuple(t,int)=
        set C.N+=1
        Print("try {C.N}")
        X=V
        (X,C.N)
Bind(B:box(t) where t:subtype(comparable))<computes>:type{_(:t)<transacts><decides>:tuple(t,rational)}=B.Match
Main():void=
    B:=box(string){V:="yes",C:=cell{}}
    F:=Bind(B)
    if(F["no"])then Print("wrong")else Print("miss {B.C.N}")
    if(F["yes"],Print("suffix"),false?)then Print("wrong")else Print("reject {B.C.N}")
    if(R:=F["yes"])then Print("hit {R(0)} {Floor(R(1))} {B.C.N}")else Print("wrong")

cell:=class{var N:int=0}
box(t:type):=class:
    V:t
    C:cell
    Match(P:tuple(a,a) where a:subtype(comparable))<transacts><decides>:a=
        set C.N+=1
        Print("try {C.N}")
        P(0)=P(1)
        P(0)
Run(B:box(t),X:u,Y:u where t:type,u:subtype(comparable))<transacts>:void=
    F:type{_(:u,:u)<transacts><decides>:u}=B.Match
    if(F[Y,X])then Print("wrong")else Print("miss {B.C.N}")
    if(F[X,X],Print("suffix"),false?)then Print("wrong")else Print("reject {B.C.N}")
    if(F[X,X])then Print("hit {B.C.N}")else Print("wrong")
Main():void=Run(box(int){V:=5,C:=cell{}},"old","new")

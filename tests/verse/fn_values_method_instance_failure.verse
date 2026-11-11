cell:=class{var N:int=0}
box(t:type):=class:
    V:t
    C:cell
    Match(X:u,Y:u where u:subtype(comparable))<transacts><decides>:u=
        set C.N+=1
        Print("try {C.N}")
        X=Y
        X
Run(B:box(t),X:u,Y:u where t:type,u:subtype(comparable))<transacts>:void=
    F:type{_(:u,:u)<transacts><decides>:u}=B.Match
    if(F[Y,X])then Print("wrong")else Print("miss {B.C.N}")
    if(F[X,X],Print("suffix"),false?)then Print("wrong")else Print("reject {B.C.N}")
    if(F[X,X])then Print("hit {B.C.N}")
Main():void=Run(box(string){V:="s",C:=cell{}},3,4)

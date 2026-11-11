cell:=class{var N:int=0}
box(t:subtype(comparable),u:type):=class:
    V:t
    Extra:u
    C:cell
    Keep(X:t)<transacts><decides>:t=
        set C.N+=1
        Print("try {C.N}")
        X=V
        X
Touch(B:box(a,b) where a:subtype(comparable),b:type)<transacts>:box(a,b)=
    set B.C.N+=1
    Print("receiver {B.C.N}")
    B
Apply(F:type{_(:a)<transacts><decides>:b},X:a where a:type,b:type)<transacts><decides>:b=F[X]
Run(B:box(a,b),Wrong:a where a:subtype(comparable),b:type)<transacts>:void=
    F:=Touch(B).Keep
    if(Y:=Apply[F,Wrong])then Print("bad")else Print("miss {B.C.N}")
    if(Y:=Apply[F,B.V],Print("suffix"),false?)then Print("bad")else Print("reject {B.C.N}")
    if(Y:=Apply[F,B.V])then Print("hit {B.C.N}")else Print("bad")
Main():void=Run(box(string,int){V:="old",Extra:=4,C:=cell{}},"new")

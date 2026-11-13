vehicle:=class<computes>{N:int=1}
car:=class<computes>(vehicle){Name:string="precise"}
Identity(X:a where a:type)<computes>:a=X
Apply(P:int,F:f,X:a,?Copy:a=F(X) where f:subtype(type{_(:a)<computes>:a}),a:type)<computes>:tuple(f,a)=(F,Copy)
Relay(S:string,F:f,X:a where a:type,f:subtype(type{_(:a)<computes>:a}))<computes>:tuple(f,a)=Apply(29,F,X)
Main():void=
    F:type{_(:car)<computes>:car}=Identity
    R:=Relay("padding",F,car{Name:="first"})
    D:=car{Name:="again"}
    S:=R(0)(D)
    Print("generic {R(1).Name} {S.Name}")

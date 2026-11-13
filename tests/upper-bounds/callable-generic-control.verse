vehicle:=class<computes>{N:int=1}
car:=class<computes>(vehicle){Name:string="precise"}
Identity(X:a where a:type)<computes>:a=X
Apply(P:int,F:type{_(:car)<computes>:car},X:car,?Copy:car=F(X))<computes>:tuple(type{_(:car)<computes>:car},car)=(F,Copy)
Relay(S:string,F:type{_(:car)<computes>:car},X:car)<computes>:tuple(type{_(:car)<computes>:car},car)=Apply(29,F,X)
Main():void=
    F:type{_(:car)<computes>:car}=Identity
    R:=Relay("padding",F,car{Name:="first"})
    D:=car{Name:="again"}
    S:=R(0)(D)
    Print("generic {R(1).Name} {S.Name}")

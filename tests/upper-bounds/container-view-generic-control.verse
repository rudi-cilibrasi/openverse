vehicle:=class<computes>{N:int=1}
car:=class<computes>(vehicle){Name:string="precise"}
Head(P:int,A:[]car,Seed:car)<computes>:tuple([]car,car)=
    V:=if(X:=A[0])then X else Seed
    (A,V)
Relay(S:string,A:[]car,Seed:car)<computes>:tuple([]car,car)=Head(29,A,Seed)
Main():void=
    C:=car{Name:="first"}
    R:=Relay("padding",array{C},car{Name:="seed"})
    Print("generic {R(0).Length} {R(1).Name}")
    E:=Relay("padding",array{},car{Name:="seed"})
    Print("empty {E(0).Length} {E(1).Name}")

vehicle:=class<computes>{N:int=1}
car:=class<computes>(vehicle){Name:string="precise"}
Head(P:int,A:t,Seed:a where t:subtype([]a),a:type)<computes>:tuple(t,a)=
    V:=if(X:=A[0])then X else Seed
    (A,V)
Relay(S:string,A:t,Seed:a where a:type,t:subtype([]a))<computes>:tuple(t,a)=Head(29,A,Seed)
Main():void=
    C:=car{Name:="first"}
    R:=Relay("padding",array{C},car{Name:="seed"})
    Print("generic {R(0).Length} {R(1).Name}")
    E:=Relay("padding",array{},car{Name:="seed"})
    Print("empty {E(0).Length} {E(1).Name}")

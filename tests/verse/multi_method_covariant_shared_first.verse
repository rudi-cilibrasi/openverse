# Shared typed dispatch suffixes retain independent class arguments and var copy-out.
animal(t:type) := class { V:t }
dog(t:type) := class(animal(t)) { Code:int }
shelter(t:type) := class:
    A:dog(t)
    B:dog(t)
    Get(S:string)<transacts>:animal(t) = A | B
kennel(t:type) := class(shelter(t)):
    Get<override>(S:string)<transacts>:dog(t) =
        Print("get {S}")
        A | B
Run(K:kennel(t),L:kennel(u) where t:type,u:type)<transacts>:tuple(dog(t),dog(u)) =
    var Total:int=0
    var ChosenA:dog(t)=K.A
    var ChosenB:dog(u)=L.A
    if(X:=K.Get("a"),set Total+=X.Code,Y:=L.Get("b"),set Total+=Y.Code,X.Code+Y.Code=22,E:[]t=Concatenate(),F:[]u=Concatenate()):
        set ChosenA=X
        set ChosenB=Y
        Print("{X.Code} {Y.Code} {Total} {E.Length} {F.Length}")
    Print("after {Total}")
    if(X:=K.Get("bad-a"),set Total+=X.Code,Y:=L.Get("bad-b"),set Total+=Y.Code,X.Code+Y.Code=999) then Print("bad") else Print("none {Total}")
    O:=option{X:=K.Get("oa"); Y:=L.Get("ob"); X.Code+Y.Code=11; (X,Y)}
    if(P:=O?) then Print("option {P(0).Code} {P(1).Code}")
    (ChosenA,ChosenB)
Main()<transacts>:void =
    A:=dog(int){V:=7,Code:=1}
    B:=dog(int){V:=8,Code:=2}
    C:=dog(string){V:="s",Code:=10}
    D:=dog(string){V:="t",Code:=20}
    P:=Run(kennel(int){A:=A,B:=B},kennel(string){A:=C,B:=D})
    Print("values {P(0).V} {P(1).V}")

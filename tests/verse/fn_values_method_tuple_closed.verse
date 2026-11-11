box:=class:
    Add(X:int,Y:int)<computes>:int=X+Y
    Sub(P:tuple(int,int))<computes>:int=P(0)-P(1)
Main():void=
    B:=box{}
    F:type{_(:tuple(int,int))<computes>:int}=B.Add
    G:type{_(:int,:int)<computes>:int}=B.Sub
    Print("{F((3,4))} {G(9,2)}")

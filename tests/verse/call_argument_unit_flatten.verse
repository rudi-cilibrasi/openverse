# Empty and singleton tuple producers retain evaluation before the body.
Unit():tuple()=Print("unit")
Zero():int=block{Print("body");7}
Single(P:tuple(u) where u:type)<computes>:tuple(u)=P
Take(X:int):int=block{Print("single body");X}
worker:=class:
    (worker:)Zero():int=block{Print("method body");8}
Main():void=
    Print("{Zero(Unit())}")
    Wrap:type{_(:int)<computes>:tuple(int)}=Single
    Print("{Take(Wrap(9))}")
    W:=worker{}
    Print("{W.Zero(Unit())}")

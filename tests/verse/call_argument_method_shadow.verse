F():int=7
box(t:type):=struct<computes>{N:int=7}
Make(?N:int=0 where t:type)<computes>:box(t)=box(t){N:=N}
host:=class:
    F(X:t where t:type)<computes>:t=X
    G(P:tuple(box(int)))<computes>:int=P(0).N
    Run()<computes>:int=G(F(Make()))
Main():void=Print("{host{}.Run()}")

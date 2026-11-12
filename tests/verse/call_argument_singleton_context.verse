# Singleton tuple elements retain their context through blocks and branches.
F(P:tuple([]int))<computes>:int=P(0).Length
G(P:tuple(?int))<computes>:int=if(X:=P(0)?)then X else -1
Id(X:t where t:type)<computes>:t=X
H(P:tuple([]t),?V:t where t:type)<computes>:int=P(0).Length
box(t:type):=struct<computes>{N:int=7}
Make(?N:int=0 where t:type)<computes>:box(t)=box(t){N:=N}
Box(P:tuple(box(int)))<computes>:int=P(0).N
Main():void=
    Print("{F(block{Print("arg");array{}})}")
    Print("{F(if(1=1){array{}}else{array{1}})}")
    Print("{F(Id(array{}))}")
    Print("{G(false)} {H(array{},?V:=7)}")
    Print("{Box(Make())} {Box(Id(Id(Make())))}")

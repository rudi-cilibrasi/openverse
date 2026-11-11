Nat(N:int)<transacts><decides>:int =
    Print("visit {N}")
    N | Nat[N+1]
i1 := interface:
    M(N:int):int
i2 := interface:
    M(N:int):int
base := class(i1,i2):
    (i1:)M<override>(N:int):int=1
    (i2:)M<override>(N:int):int=3
mid := class(base):
    (i1:)M<override>(N:int):int=if(X:=Nat[N],X>(super:)M(N)) then X else -1
    (i2:)M<override>(N:int):int=if(X:=Nat[N],X>(super:)M(N)) then X else -1
leaf := class(mid):
    (i1:)M<override>(N:int):int=99
    (i2:)M<override>(N:int):int=99
Main():void=
    M:=mid{}
    A:i1=M
    B:i2=M
    Print("i1 {A.M(0)}")
    Print("i2 {B.M(0)}")

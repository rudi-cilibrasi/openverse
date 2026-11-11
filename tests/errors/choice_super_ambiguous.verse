# expect: is ambiguous here
Nat(N:int)<transacts><decides>:int=
    Print("visit {N}")
    N|Nat[N+1]
i1 := interface:
    M(N:int):int
i2 := interface:
    M(N:int):int
base := class(i1,i2):
    (i1:)M<override>(N:int):int=1
    (i2:)M<override>(N:int):int=3
sub := class(base):
    M<override>(N:int):int=if(X:=Nat[N],X>(super:)M(N)) then X else -1
Main():void=Print("{sub{}.M(0)}")

# expect: cannot be used as a value
Nat(N:int)<transacts><decides>:int=
    Print("visit {N}")
    N|Nat[N+1]
base := class:
    Limit():int=1
sub := class(base):
    Limit<override>():int=if(X:=Nat[0],F:type{_():int}=(super:)Limit) then X else -1
Main():void=Print("{sub{}.Limit()}")

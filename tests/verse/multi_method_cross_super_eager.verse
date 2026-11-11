# Non-generator recursion keeps scalar super context in generated array code.
base := class:
    Step(X:int)<computes>:int = X+10
child := class(base):
    Values(N:int)<computes>:int =
        if(N<=0)then 1|2 else (super:)Step(Self.Values(N-1))
Main():void =
    for(V:=child{}.Values(2)): Print("{V}")
    if(V:=first{child{}.Values(2)})then Print("first {V}")

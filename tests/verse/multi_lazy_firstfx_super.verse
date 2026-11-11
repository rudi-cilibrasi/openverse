Nat(N:int)<transacts><decides>:int =
    Print("at {N}")
    N | Nat[N + 1]
base := class:
    Lim()<computes>:int = 2
sub := class(base):
    Lim<override>()<computes>:int = 5
    Find():int = if (X := Nat[0], X > (super:)Lim()) then X else -1
Main():void = Print("{sub{}.Find()}")

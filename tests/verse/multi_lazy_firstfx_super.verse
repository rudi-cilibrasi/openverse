Nat(N:int)<transacts><decides>:int =
    Print("at {N}")
    N | Nat[N + 1]
first_probe := struct{}
base := class:
    Lim()<computes>:int = 2
    # ((super:)M is only in an override of M, the Book's rule: the methods
    # that call it are overloads of M that override these)
    Lim(Probe:first_probe):int = 0
sub := class(base):
    Lim<override>()<computes>:int = 5
    Lim<override>(Probe:first_probe):int = if (X := Nat[0], X > (super:)Lim()) then X else -1
Main():void = Print("{sub{}.Lim(first_probe{})}")

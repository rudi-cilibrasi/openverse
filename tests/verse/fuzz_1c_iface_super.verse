# internal error: i4.M does not pass Prog.checkTypes. i4 overrides i1's default
# and calls (super:); no class is below i4, but one is below i1. (With c below
# i4 instead, or with no class at all, it runs.)
i1 := interface:
    M(P:int):int = P
i4 := interface(i1):
    M<override>(P:int):int = (super:)M(P)
c := class(i1):
    H:int = 14
Main():void =
    Print("x")

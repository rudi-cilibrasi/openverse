# expect: this arm of race cannot suspend
# A call of a function value whose type does not suspend cannot suspend
W(D:float)<suspends>:int =
    Sleep(D)
    1
I(D:float):int = 2
Run(F:type{_(:float)<suspends>:int}, G:type{_(:float):int})<suspends>:void =
    X := race:
        F(1.0)
        G(2.0)
    Print("{X}")
Main()<suspends>:void =
    Run(W, I)

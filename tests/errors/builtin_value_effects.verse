# expect: 5:18: expected type{_(:float)<computes>:float}, found type{_(:float)<reads>:float}
# Sinh has the effect <reads>, so it is no value of a <computes> function type.
Twice(F(:float)<computes>:float, X:float):float = F(F(X))
Main():void =
    Print("{Twice(Sinh, 1.0)}")

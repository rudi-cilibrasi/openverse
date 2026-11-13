# A built-in of one signature is a function like any other: named as a value
# (the Book's tests pass Sin to a parameter F(:float):float), it is a
# function value of its type and effects.
CheckSpecials(F(:float):float, AtMinusInf:float, AtInf:float)<decides>:void =
    F(-Inf) = AtMinusInf and F(Inf) = AtInf and F(NaN) = NaN
Twice(F(:float)<reads>:float, X:float)<reads>:float = F(F(X))
Rounded(F(:float)<decides>:int, X:float):int = if (R := F[X]) then R else -1
Main():void =
    if (CheckSpecials[Sqrt, NaN, Inf], CheckSpecials[Sin, NaN, NaN], CheckSpecials[Sinh, -Inf, Inf]):
        G := Exp
        Print("{G(0.0)} {Twice(Sqrt, 16.0)} {Twice(Cosh, 0.0)} {Rounded(Round, 2.5)} {Rounded(Int, NaN)} {Sqrt(9.0)}")

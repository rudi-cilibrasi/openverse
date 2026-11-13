# Clamp(Val, A, B), the median of the three, so the order of A and B does not
# matter (the Book's Runtime API), of ints or of floats, among which NaN
# orders above +Inf (Epic's API); Sgn(X) of an int or a float, NaN of NaN;
# and F.IsFinite[] of a float, F unless it is infinite or NaN.
Show(X:float):string = if (X = NaN) then "NaN" else "{X}"
Main():void =
    Print("{Clamp(5, -2, 2)} {Clamp(5, 2, -2)} {Clamp(-5, 2, -2)} {Clamp(1, 2, -2)}")
    Print("{Clamp(5.0, 2.0, -2.0)} {Clamp(-Inf, -2.0, 2.0)} {Show(Clamp(NaN, -2.0, 2.0))} {Show(Clamp(5.0, NaN, 2.0))} {Show(Clamp(NaN, 1.0, NaN))}")
    Print("{Sgn(-7)} {Sgn(0)} {Sgn(9)} {Sgn(-Inf)} {Sgn(0.0)} {Sgn(0.25)} {Show(Sgn(NaN))}")
    if (F := (2.5).IsFinite[], not Inf.IsFinite[], not NaN.IsFinite[]):
        Print("{F}")

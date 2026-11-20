# Min, Max, Clamp, Abs and Sgn of floats, with NaN and infinite arguments.
# Tests LANGUAGE.md, float: "Min and Max give NaN when either is NaN";
# Built-ins: "Clamp(Val, A, B) (the median of the three, of ints or of
# floats, NaN ordering above +Inf)", "Sgn(X) (-1, 0 or 1 of an int or a
# float, NaN of NaN)". Epic's digest documents the same for Clamp and Min.
# OpenVerse prints (Lean and C agree):
#   min NaN NaN -Inf -2.500000 | max NaN NaN Inf 2.500000
#   clamp 1.000000 5.000000 0.000000 0.500000
#   abs 2.500000 Inf NaN sgn -1.000000 0.000000 NaN 1.000000
Main():void =
    Z:float = 0.0
    N:float = Z / Z
    Print("OVPROBE min {Min(N, 1.0)} {Min(1.0, N)} {Min(-Inf, 3.0)} {Min(2.5, -2.5)}")
    Print("OVPROBE max {Max(N, 1.0)} {Max(1.0, N)} {Max(Inf, 3.0)} {Max(2.5, -2.5)}")
    Print("OVPROBE clamp {Clamp(N, 0.0, 1.0)} {Clamp(5.0, 10.0, 1.0)} {Clamp(-3.0, 0.0, 1.0)} {Clamp(0.5, N, 0.0)}")
    Print("OVPROBE abs {Abs(-2.5)} {Abs(-Inf)} {Abs(N)} sgn {Sgn(-3.5)} {Sgn(Z)} {Sgn(N)} {Sgn(Inf)}")

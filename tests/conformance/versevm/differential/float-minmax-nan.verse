# Min, Max, Clamp, Abs and Sgn of floats, with NaN and infinite arguments.
# Tests LANGUAGE.md, float: "Min and Max give NaN when either is NaN";
# Built-ins: "Clamp(Val, A, B) (the median of the three, of ints or of
# floats, NaN ordering above +Inf)", "Sgn(X) (-1, 0 or 1 of an int or a
# float, NaN of NaN)". Epic's digest documents the same for Clamp and Min.
# OpenVerse (#724) printed, until Epic's result below:
#   min NaN NaN -Inf -2.500000 | max NaN NaN Inf 2.500000
#   clamp 1.000000 5.000000 0.000000 0.500000
#   abs 2.500000 Inf NaN sgn -1.000000 0.000000 NaN 1.000000
# Epic's Verse VM (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, "Use
# Verse VM" on, 2026-11-20) printed
#   min NaN NaN -Inf -2.500000 | max NaN NaN Inf 2.500000
#   clamp NaN 5.000000 0.000000 NaN
#   abs 2.500000 Inf NaN sgn -1.000000 0.000000 NaN 1.000000
# Clamp of a NaN is NaN (float-clamp-nan asks each position). OpenVerse now
# prints it too (#724, Lean and C agreeing).
Main():void =
    Z:float = 0.0
    N:float = Z / Z
    Print("OVPROBE min {Min(N, 1.0)} {Min(1.0, N)} {Min(-Inf, 3.0)} {Min(2.5, -2.5)}")
    Print("OVPROBE max {Max(N, 1.0)} {Max(1.0, N)} {Max(Inf, 3.0)} {Max(2.5, -2.5)}")
    Print("OVPROBE clamp {Clamp(N, 0.0, 1.0)} {Clamp(5.0, 10.0, 1.0)} {Clamp(-3.0, 0.0, 1.0)} {Clamp(0.5, N, 0.0)}")
    Print("OVPROBE abs {Abs(-2.5)} {Abs(-Inf)} {Abs(N)} sgn {Sgn(-3.5)} {Sgn(Z)} {Sgn(N)} {Sgn(Inf)}")

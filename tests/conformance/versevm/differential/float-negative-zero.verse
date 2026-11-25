# Negative zero: its ToString, the sign of 1/x, and its equality with 0.0.
# Tests LANGUAGE.md, float: "it has one NaN, which equals itself, and no
# negative zero" and "-0.0 is 0.0, which prints 0.000000" (the readings
# audit, "Negative zero": the Book disagrees with itself; ch. 11 says zero
# has no sign, the API says negating zero "genuinely produces -0.0" and that
# it prints differently from 0.0). With IEEE negative zeros, a prints
# -0.000000 for each value and b prints -Inf for each quotient.
# OpenVerse prints (Lean and C agree):
#   a 0.000000 0.000000 0.000000 0.000000 | b Inf Inf Inf Inf
#   c equal not less
Main():void =
    Z:float = 0.0
    N:float = -Z
    M:float = Z * -1.0
    U:float = -1.0e-300 * 1.0e-300
    Print("OVPROBE a {N} {M} {U} {-0.0}")
    Print("OVPROBE b {1.0 / N} {1.0 / M} {1.0 / U} {1.0 / Z}")
    E := if (N = Z) then "equal" else "different"
    L := if (N < Z) then "less" else "not less"
    Print("OVPROBE c {E} {L}")

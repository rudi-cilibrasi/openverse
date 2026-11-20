# The float math functions at ordinary values and at the edges of their
# domains.
# Tests LANGUAGE.md, float: "their special values are C's (Sqrt(-1.0) and
# Ln(-1.0) are NaN, Ln(0.0) is -Inf, Pow(0.0, 0.0) is 1.0, Sin(Inf) is NaN).
# ArcSin and ArcCos clamp their argument to [-1, 1] (the Book leaves that
# case to the engine)" (an OpenVerse choice: C's asin(2.0) is NaN); "Log
# divides Lns, so Log(10.0, 1000.0) is 2.9999999999999996". The values are
# chosen so that six decimals hide last-bit differences between libms.
# OpenVerse prints (Lean and C agree):
#   a 1.414214 1024.000000 2.718282 2.302585 3.141593
#   b NaN -Inf NaN 1.000000 NaN | c 1.570796 3.141593 1.570796 0.785398
#   d 3.000000 inexact 2
Main():void =
    Print("OVPROBE a {Sqrt(2.0)} {Pow(2.0, 10.0)} {Exp(1.0)} {Ln(10.0)} {PiFloat}")
    Print("OVPROBE b {Sqrt(-1.0)} {Ln(0.0)} {Ln(-1.0)} {Pow(0.0, 0.0)} {Sin(Inf)}")
    Print("OVPROBE c {ArcSin(2.0)} {ArcCos(-2.0)} {ArcSin(1.0)} {ArcTan(1.0, 1.0)}")
    L:float = Log(10.0, 1000.0)
    R := if (L = 3.0) then "exact" else "inexact"
    FL := Floor[L] or -1
    Print("OVPROBE d {L} {R} {FL}")

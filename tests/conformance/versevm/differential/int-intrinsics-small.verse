# Abs, Sgn, Min, Max and Clamp of ints inside 64 bits, Clamp with its bounds
# in either order.
# Tests LANGUAGE.md, Built-ins: "Clamp(Val, A, B) (the median of the three)";
# float: "the order of A and B does not matter"; Epic's digest: "Robustly
# handles different argument orderings. Returns the median". A Clamp written
# Min(Max(Val, A), B) would give 1 for Clamp(5, 10, 1).
# OpenVerse prints (Lean and C agree):
#   abs 5 0 7 sgn -1 0 1 | minmax -2 3 -9223372036854775807 4
#   clamp 5 5 1 10 7
Main():void =
    Print("OVPROBE abs {Abs(-5)} {Abs(0)} {Abs(7)} sgn {Sgn(-3)} {Sgn(0)} {Sgn(9)}")
    Print("OVPROBE minmax {Min(3, -2)} {Max(3, -2)} {Min(-9223372036854775807, 0)} {Max(4, 4)}")
    Print("OVPROBE clamp {Clamp(5, 1, 10)} {Clamp(5, 10, 1)} {Clamp(-3, 1, 10)} {Clamp(30, 10, 1)} {Clamp(7, 7, 7)}")

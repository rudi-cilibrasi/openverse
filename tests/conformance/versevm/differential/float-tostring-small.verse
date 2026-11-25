# ToString of small floats: what six decimals keep, and the sign of a tiny
# negative value.
# Tests LANGUAGE.md, float: "a - whenever the float is negative, also when
# every digit is zero (-0.000000 for -1.0e-300)"; the Book's API: "every
# subnormal prints as 0.000000", "a tiny negative value prints as -0.000000".
# A formatter that drops the sign of a zero rendering would print 0.000000
# in b. In c the second and third products underflow to a negative zero in
# IEEE arithmetic, which openverse does not have (float-negative-zero): with
# negative zeros they print -0.000000.
# OpenVerse prints (Lean and C agree):
#   a 0.000001 0.000000 0.000001 0.000005 0.000000
#   b -0.000000 -0.000000 -0.000000 -0.000001 | c 0.000000 0.000000 0.000000
Main():void =
    Print("OVPROBE a {1.0e-6} {4.0e-7} {6.0e-7} {5.0e-6} {1.0e-300}")
    Print("OVPROBE b {-1.0e-7} {-1.0e-300} {-4.0e-7} {-6.0e-7}")
    Tiny:float = 1.0e-200
    Print("OVPROBE c {Tiny * Tiny} {-Tiny * Tiny} {Tiny * -Tiny}")

# ToString of ordinary floats through string interpolation.
# Tests LANGUAGE.md, Readings, "ToString of a float": "six digits after the
# point, the exact value rounded half to even, every integer digit, the sign
# kept"; "interpolation calls ToString (ch. 2)". The Book's ch. 2 example
# prints 98.5 for 98.5 (the shortest decimal), its API and tests 98.500000.
# Not yet observed on Epic: no probe so far has interpolated a float.
# OpenVerse prints (Lean and C agree):
#   a 1.000000 1.500000 98.500000 100.000000 -2.250000
#   b 0.300000 0.666667 -0.333333 0.100000
#   c 123456.789000 4.500000 1000.000000 0.250000
#   d 3.500000 -7.000000 49.000000 0.000000
Main():void =
    Print("OVPROBE a {1.0} {1.5} {98.5} {100.0} {-2.25}")
    Print("OVPROBE b {0.1 + 0.2} {2.0 / 3.0} {-1.0 / 3.0} {0.1}")
    Print("OVPROBE c {123456.789} {3.0 * 1.5} {1.0e3} {2.5e-1}")
    X:float = 7.0
    Print("OVPROBE d {X / 2.0} {-X} {X * X} {X - 7.0}")

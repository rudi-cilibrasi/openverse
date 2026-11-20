# ToString of ints at the top of 64 bits, negatives and zero, by
# interpolation and by a direct call. (The least int: int-tostring-min, run
# alone.)
# Tests LANGUAGE.md, Built-ins: "ToString(x) (int, ...; of an int beyond 64
# bits, the overflow error)": inside 64 bits it is the decimal digits.
# OpenVerse prints (Lean and C agree):
#   a 9223372036854775807 -9223372036854775807 0 -1 0
#   b 9223372036854775806 -9223372036854775806 -42
#   c 1000000000000 -1000000000000
Main():void =
    Top:int = 9223372036854775807
    Print("OVPROBE a {Top} {-Top} {0} {-1} {-0}")
    Print("OVPROBE b " + ToString(Top - 1) + " " + ToString(-Top + 1) + " " + ToString(-42))
    Print("OVPROBE c {1000000 * 1000000} {-1000000 * 1000000}")

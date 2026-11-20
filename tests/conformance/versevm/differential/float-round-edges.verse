# Floor, Ceil and Int of floats at the edges of the 64-bit range (run alone,
# last: a native that checks the range more strictly would stop the session
# with ErrRuntime_IntegerBoundsExceeded, as Floor[1.0e19] does,
# followup-int/int-float-floor-big).
# Tests LANGUAGE.md, float: "a result out of the int range is the overflow
# error (the API's integer-bounds error)": -2^63 is a double exactly and in
# range, and so are 2^62 and -4.5e18; 9223372036854774784.0 (2^63 - 1024) is
# the largest double below 2^63.
# OpenVerse prints (Lean and C agree):
#   before edges
#   edges -9223372036854775808 4611686018427387904 -4500000000000000000
#   largest below 2^63 9223372036854774784
Main()<suspends>:void =
    Print("OVPROBE before edges")
    Sleep(0.0)
    if (E := Floor[-9223372036854775808.0], F := Ceil[4611686018427387904.0], G := Int[-4.5e18]):
        Print("OVPROBE edges {E} {F} {G}")
    else:
        Print("OVPROBE edges failed")
    Sleep(0.0)
    if (H := Floor[9223372036854774784.0]):
        Print("OVPROBE largest below 2^63 {H}")

# ToString of the least 64-bit int, -2^63 (run alone, last: a native
# ToString whose range check excludes -2^63 would stop the session with
# "Value exceeds the range of a 64 bit integer", as it does past 64 bits,
# followup-int/int-tostring-direct).
# Tests LANGUAGE.md, int: "What needs 64 bits checks for them. ToString of
# an int beyond 64 bits ... is the overflow error": -2^63 is within them.
# OpenVerse prints (Lean and C agree):
#   before min | interpolated -9223372036854775808
#   direct -9223372036854775808
Main()<suspends>:void =
    Print("OVPROBE before min")
    Sleep(0.0)
    Least:int = -9223372036854775807 - 1
    Print("OVPROBE interpolated {Least}")
    Sleep(0.0)
    Print("OVPROBE direct " + ToString(Least))

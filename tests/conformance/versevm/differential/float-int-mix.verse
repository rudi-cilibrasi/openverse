# Multiplying an int by a float (and a float by an int), the one int/float
# mix, and a float compared after it.
# Tests LANGUAGE.md, float: "No int converts to a float implicitly. The one
# mix is *: Count * 1.5"; int: "X * 1.5 converts the int to the nearest
# double, ties to even" (Epic agrees: followup-int/int-float-tie, past 64
# bits; here inside them). 2^53 + 1 is not a double: it rounds to 2^53.
# OpenVerse prints (Lean and C agree):
#   a 7.500000 7.500000 -0.750000 0.500000
#   b 9007199254740992.000000 9007199254740992.000000 4503599627370496.000000
#   c rounded
Main():void =
    Count:int = 5
    Print("OVPROBE a {Count * 1.5} {1.5 * Count} {-3 * 0.25} {Count * 0.1}")
    Big:int = 9007199254740993
    Print("OVPROBE b {Big * 1.0} {(Big - 1) * 1.0} {Big * 0.5}")
    R := if (Big * 1.0 = 9007199254740992.0) then "rounded" else "kept"
    Print("OVPROBE c {R}")

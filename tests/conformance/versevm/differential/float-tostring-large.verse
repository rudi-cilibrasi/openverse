# ToString of large floats: every integer digit of the exact binary value.
# Tests LANGUAGE.md, float: "every digit before the point (1.0e100 prints its
# exact binary value, 101 digits, then .000000)"; the Book's tests
# (FloatToString.versetest:22) "1234567890123456.000000". 1.0e23's nearest
# double is 99999999999999991611392. A formatter that rounds to 17
# significant digits would print 1.0e23 as 100000000000000000000000.000000,
# and one with an exponent form something else again.
# OpenVerse prints (Lean and C agree):
#   a 1000000000000000.000000 1234567890123456.000000 9007199254740992.000000
#   b 10000000000000000000000.000000 99999999999999991611392.000000 -4000000000000000000.000000
#   c 10000000000000000159028911097599180468360808563945281389781327557747838772170381060813469985856815104.000000
#   d Inf -Inf Inf
Main():void =
    Print("OVPROBE a {1.0e15} {1234567890123456.0} {9007199254740993.0}")
    Print("OVPROBE b {1.0e22} {1.0e23} {-4.0e18}")
    Print("OVPROBE c {1.0e100}")
    Big:float = 1.0e300
    Print("OVPROBE d {Big * Big} {-Big * Big} {Big / 1.0e-300}")

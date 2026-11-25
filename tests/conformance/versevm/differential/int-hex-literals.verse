# Hexadecimal int literals, upper and lower case, up to the 64-bit maximum.
# Tests LANGUAGE.md, Supported, Literals: "int (decimal, 0x hex; must fit in
# 64 bits)".
# OpenVerse prints (Lean and C agree):
#   127 255 0 9223372036854775807 -16
Main():void =
    Print("OVPROBE {0x7F} {0xff} {0x0} {0x7FFFFFFFFFFFFFFF} {-0x10}")

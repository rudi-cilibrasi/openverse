# ToString called directly on an int, a float, a char and a string, and
# joined with +.
# Tests LANGUAGE.md, Built-ins: "ToString(x) (int, float, char, char32,
# string ...)"; Epic's digest declares ToString of int, float, char and
# string.
# OpenVerse prints (Lean and C agree):
#   -5/0.500000/q/s 15
Main():void =
    S:string = ToString(-5) + "/" + ToString(0.5) + "/" + ToString('q') + "/" + ToString("s")
    Print("OVPROBE {S} {S.Length}")

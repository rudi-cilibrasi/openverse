# Interpolation of each kind of value that has a ToString: int, float, char,
# string, and expressions, adjacent in one string literal.
# Tests LANGUAGE.md, Literals: "strings with escapes and {expr}
# interpolation"; Readings, "ToString of a float": "interpolation calls
# ToString (ch. 2)". (Nested string literals: str-interp-nested.)
# OpenVerse prints (Lean and C agree):
#   a -122.500000zstr [-10] [5.000000] [12] | b 3 z 3 143
Main():void =
    I:int = -12
    F:float = 2.5
    C:char = 'z'
    S:string = "str"
    Print("OVPROBE a {I}{F}{C}{S} [{I + 2}] [{F * 2.0}] [{-I}]")
    Print("OVPROBE b {S.Length} {ToString(C)} {array{1, 2, 3}.Length} {I * I - 1}")

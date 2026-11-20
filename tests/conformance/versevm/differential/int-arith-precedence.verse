# Integer arithmetic precedence and associativity, with unary minus.
# Tests LANGUAGE.md, Operators: "* + -, unary -"; the Book's ch. 4
# precedence table (* above +, both left to right).
# OpenVerse prints (Lean and C agree):
#   a 14 20 5 24 75 | b 9 2 5 -5 -6 | c 3 -7 -5
Main():void =
    X:int = 3
    Print("OVPROBE a {2 + 3 * 4} {(2 + 3) * 4} {10 - 3 - 2} {2 * 3 * 4} {100 - 10 * 2 - 5}")
    Print("OVPROBE b {-X * -X} {-X + 5} {2 - -3} {-(2 + X)} {- X - X}")
    Print("OVPROBE c {X * X - X * 2} {1 - X * X + 1} {-2 * 3 + 1}")

# Escapes in string literals, measured by length as well as printed.
# Tests LANGUAGE.md, Literals: "strings with escapes and {expr}
# interpolation". Each escape is one char, so the lengths are 3. A tab is
# printed between the brackets of t (written \t in the line below).
# OpenVerse prints (Lean and C agree):
#   q [a"b] 3 b [a\b] 3 l [a{b] 3 r [a}b] 3 | t [a\tb] 3
Main():void =
    Q:string = "a\"b"
    B:string = "a\\b"
    L:string = "a\{b"
    R:string = "a\}b"
    T:string = "a\tb"
    Print("OVPROBE q [{Q}] {Q.Length} b [{B}] {B.Length} l [{L}] {L.Length} r [{R}] {R.Length}")
    Print("OVPROBE t [{T}] {T.Length}")

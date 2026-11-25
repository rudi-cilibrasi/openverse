# case on strings, the empty string included, with a default.
# Tests LANGUAGE.md, Control: "case with literal or computed scalar patterns
# and _" (a string literal as a pattern). Epic's compiler may take only
# scalar patterns.
# OpenVerse prints (Lean and C agree):
#   short long empty unknown
Greet(S:string):string =
    case (S):
        "hi" => "short"
        "hello" => "long"
        "" => "empty"
        _ => "unknown"

Main():void =
    Print("OVPROBE {Greet("hi")} {Greet("hello")} {Greet("")} {Greet("hey")}")

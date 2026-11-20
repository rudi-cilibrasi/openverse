# case on ints and chars, with defaults. (On strings: case-string.)
# Tests LANGUAGE.md, Control: "case with literal or computed scalar patterns
# and _".
# OpenVerse prints (Lean and C agree):
#   int zero one hundred other | char a space else
IntName(X:int):string =
    case (X):
        0 => "zero"
        1 => "one"
        100 => "hundred"
        _ => "other"

Kind(C:char):string =
    case (C):
        'a' => "a"
        ' ' => "space"
        _ => "else"

Main():void =
    Print("OVPROBE int {IntName(0)} {IntName(1)} {IntName(100)} {IntName(7)}")
    Print("OVPROBE char {Kind('a')} {Kind(' ')} {Kind('b')}")

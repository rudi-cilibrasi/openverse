# Evaluation order: a call's arguments, the operands of operators of mixed
# precedence, an array, a tuple, a map and an interpolated string, each
# recorded in a log as it is evaluated.
# Tests LANGUAGE.md, Effect contracts and Functions: arguments evaluated
# "positional, then named as written, then defaults"; Operators: operands
# left to right. Expected (left to right throughout): 1 2 3 | 4 5 6 | ...
# OpenVerse prints (Lean and C agree):
#   123 456 789 12345678 123 values 34 47 123
trace := class:
    var Trail:string = ""

Mark(T:trace, N:int)<transacts>:int =
    set T.Trail += "{N}"
    N

Three(A:int, B:int, C:int):int = A + B + C

Main():void =
    T := trace{}
    Three(Mark(T, 1), Mark(T, 2), Mark(T, 3))
    set T.Trail += " "
    X := Mark(T, 4) + Mark(T, 5) * Mark(T, 6)
    set T.Trail += " "
    Y := Mark(T, 7) * Mark(T, 8) - Mark(T, 9)
    set T.Trail += " "
    Arr := array{Mark(T, 1), Mark(T, 2)}
    Tup := (Mark(T, 3), Mark(T, 4))
    M := map{Mark(T, 5) => Mark(T, 6), Mark(T, 7) => Mark(T, 8)}
    set T.Trail += " "
    S := "{Mark(T, 1)}{Mark(T, 2)}{Mark(T, 3)}"
    Print("OVPROBE {T.Trail} values {X} {Y} {S}")

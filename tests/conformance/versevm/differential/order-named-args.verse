# Evaluation order of named arguments written in another order than the
# parameters, and when defaults are evaluated.
# Tests LANGUAGE.md, Functions: "named parameters ?P:t = default passed as
# ?P := e, after the positional arguments (... positional, then named as
# written, then defaults; ... a default is evaluated at the call". In
# parameter order instead, the first log would be 132.
# OpenVerse prints (Lean and C agree):
#   123 45 values 1327 4005 9007
trace := class:
    var Trail:string = ""

Mark(T:trace, N:int)<transacts>:int =
    set T.Trail += "{N}"
    N

Fn(X:int, ?A:int = 0, ?B:int = 0, ?C:int = 7):int = X * 1000 + A * 100 + B * 10 + C

Main():void =
    T := trace{}
    R1 := Fn(Mark(T, 1), ?B := Mark(T, 2), ?A := Mark(T, 3))
    set T.Trail += " "
    R2 := Fn(Mark(T, 4), ?C := Mark(T, 5))
    Print("OVPROBE {T.Trail} values {R1} {R2} {Fn(9)}")

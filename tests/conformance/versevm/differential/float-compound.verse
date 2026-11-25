# Compound float assignment: accumulating 0.1 ten times, and /= by zero.
# Tests LANGUAGE.md, float: "+ - * /, unary -, and set +=, -=, *=, /=.
# Dividing by zero gives Inf, -Inf or NaN; it does not fail". The sum of ten
# 0.1s is 0.9999999999999999, which prints 1.000000 but is not 1.0.
# OpenVerse prints (Lean and C agree):
#   sum 1.000000 not equal 9999999999999998.000000 | div Inf -Inf
Main():void =
    var F:float = 0.0
    for (I := 1..10):
        set F += 0.1
    E := if (F = 1.0) then "equal" else "not equal"
    Print("OVPROBE sum {F} {E} {F * 1.0e16}")
    var G:float = 3.0
    set G /= 0.0
    set G -= 1.0
    var H:float = -2.0
    set H *= Inf
    Print("OVPROBE div {G} {H}")

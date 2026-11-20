# An if with several clauses: bindings flow left to right, the first failing
# clause sends control to else, and else-if chains pick the first success.
# Tests LANGUAGE.md, Control: "if/else if/else"; Failure: an if condition is
# one failure context, its clauses in order.
# OpenVerse prints (Lean and C agree):
#   a 3 4 12 / else | b negative zero small even small odd large
Classify(X:int):string =
    if (X < 0) then "negative"
    else if (X = 0) then "zero"
    else if (X < 10, Mod[X, 2] = 0) then "small even"
    else if (X < 10) then "small odd"
    else "large"

Main():void =
    A:[]int = array{3, 4}
    R := if (I := A[0], J := A[I - 2], K := I * J, K > 10) then "{I} {J} {K}" else "else"
    S := if (I := A[0], J := A[I], K := I * J) then "{K}" else "else"
    Print("OVPROBE a {R} / {S}")
    Print("OVPROBE b {Classify(-4)} {Classify(0)} {Classify(6)} {Classify(7)} {Classify(12)}")

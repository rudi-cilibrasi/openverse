# and: both operands must succeed; the value is the right one's (Book of
# Verse §5.5). Each operand is its own scope: names defined on the left are
# not visible on the right, and names from either side do not escape.

Main():void =
    A := array{10, 20, 30}
    if (A[0] > 0 and A[2] > 20) { Print("both succeed") }
    if (A[0] > 0 and A[5] > 0) { Print("unreachable") } else { Print("the right fails") }
    # X on the left and X on the right are different names in different scopes
    if ((X := A[0]) = 10 and (X := A[1]) = 20) { Print("X twice, one per operand") }
    # a failure on the right rolls back the left's writes
    var N:int = 0
    if (set N += 1, N > 0 and N > 5) { Print("unreachable") }
    Print("N = {N}")
    V := A[1] > 0 and A[2] or 0
    W := A[9] > 0 and A[2] or 0
    Print("V = {V}, W = {W}")
    if (A[0] > 0 and A[1] > 0 and A[2] > 0) { Print("a chain of and") }

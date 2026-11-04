# Failure, failure contexts and rollback (Book of Verse ch. 8).
IsPositive(X:int)<decides>:int = X > 0

Main():void =
    var Attempts:int = 0
    # A failed condition rolls back its writes (and its output).
    if (set Attempts += 1, Print("speculative"), Attempts > 100):
        Print("unreachable")
    else:
        Print("rolled back: Attempts = {Attempts}")
    # A successful condition commits them.
    if (set Attempts += 1, Attempts > 0):
        Print("committed: Attempts = {Attempts}")
    # Comparisons return their left operand.
    if (L := (0 < 10)):
        Print("0 < 10 gives {L}")
    # Chains check every pair and return the leftmost operand.
    V:int = 5
    if (0 <= V <= 9) then Print("5 is a digit") else Print("5 is not a digit")
    if (0 <= V <= 3) then Print("5 <= 3?!") else Print("5 is not <= 3")
    # not, or, option{}, logic{}, ?
    if (not IsPositive[-3]) { Print("-3 is not positive") }
    W := IsPositive[-1] or 42
    Print("or fallback: {W}")
    MaybeX:?int = option{IsPositive[7]}
    if (X := MaybeX?) { Print("option holds {X}") }
    None:?int = option{IsPositive[-7]}
    if (None?) then Print("bad") else Print("empty option")
    B := logic{IsPositive[1]}
    if (B?) { Print("logic{} is true") }
    # not discards effects even when its operand succeeds
    var Count:int = 0
    if (not not (set Count = 99, IsPositive[1])) { Print("Count after not not: {Count}") }

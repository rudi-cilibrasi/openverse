# A method's `set C += 1` is checked addition: at the longest int (#724:
# 2^(2^20) - 1; on 64-bit ints, 2^63 - 1) it stops the program with the
# overflow error there, before the method returns, so before its caller goes
# on (`t2` is not printed); fuzz-model-mv seed 4594, whose model had it after
# The longest int, 2^(2^20) - 1: one more is the overflow error (#724).
MaxInt()<computes>:int =
    var H:int = 2
    for (I := 1..19):
        set H *= H
    (H - 1) * (H + 1)
ctr := class:
    var C:int = 0
    Next()<transacts>:int =
        set C += 1
        C - 1
    Add(X:int)<transacts>:int =
        set C += X
        C
Tell(S:string, X:int):int =
    Print(S)
    X
Main():void =
    K := ctr{C := MaxInt() - 1}
    if (K.Add(Tell("t1", K.Next()) * 0) > 0) then Print("added")
    if (K.Add(Tell("t2", K.Next())) > 0) then Print("unreachable")

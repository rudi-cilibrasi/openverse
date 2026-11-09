# a clause changing an object, where the first success is taken: kept for the calls on the way to the value taken (#246 step 2)
cell := class:
    var V:int = 0
Count(C:cell, N:int)<transacts><decides>:int =
    N > 0
    set C.V += 1
    N | Count[C, N - 1]
Main():void =
    C := cell{}
    if (X := Count[C, 3], X < 2):
        Print("{X} {C.V}")

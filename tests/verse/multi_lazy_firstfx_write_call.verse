# a clause calling a function that changes an object, where the first success is taken (#246 step 2)
cell := class:
    var V:int = 0
Bump(C:cell)<transacts>:void =
    set C.V += 1
Count(C:cell, N:int)<transacts><decides>:int =
    N > 0
    Bump(C)
    N | Count[C, N - 1]
Main():void =
    C := cell{}
    if (X := Count[C, 3], X < 2):
        Print("{X} {C.V}")

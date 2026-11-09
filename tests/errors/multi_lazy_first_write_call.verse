# expect: 13:18: Count has several values, is recursive and may change an object (Bump may) in its clauses
# (#246) a clause that calls a function that may change an object
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

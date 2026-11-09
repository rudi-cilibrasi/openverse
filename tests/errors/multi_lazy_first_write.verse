# expect: 11:18: Count has several values, is recursive and may change an object in its clauses
# (#246) a clause that changes an object: in an if, kept for the values the if rejects
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

# a generator whose clauses change an object, in a for: kept for a value its filter rejects, as a for keeps its clauses' effects before a choice (#246)
cell := class:
    var V:int = 0
Count(C:cell, N:int)<transacts><decides>:int =
    N > 0
    set C.V += 1
    N | Count[C, N - 1]
Main():void =
    C := cell{}
    for (X := Count[C, 3], X <> 2):
        Print("{X} {C.V}")
    Print("{C.V}")

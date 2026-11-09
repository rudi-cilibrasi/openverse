# expect: 10:18: Count has several values, is recursive and may print (Show does) in its clauses, its conditions or the arguments of its calls of itself
# (#246) the argument of its call of itself prints, through a function
Show(N:int)<computes>:int =
    Print("show {N}")
    N
Count(N:int)<computes><decides>:int =
    N > 0
    N | Count[Show(N) - 1]
Main():void =
    if (X := Count[3], X < 2):
        Print("{X}")

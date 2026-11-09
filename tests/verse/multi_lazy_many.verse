# a generator with 20000 values in a for: collected in linear time and space (#246)
Upto(A:int, B:int)<computes><decides>:int =
    A <= B
    A | Upto[A + 1, B]
Main():void =
    var S:int = 0
    for (X := Upto[1, 20000]) { set S += X }
    Print("{S}")

# a return from a for over a generator, a set in its body, and a set in an if's clause after it, undone for the values the if rejects (#246)
Upto(A:int, B:int)<computes><decides>:int =
    A <= B
    A | Upto[A + 1, B]
Find(T:int):int =
    for (X := Upto[1, 10]):
        if (X * X > T) then return X
    0
Main():void =
    Print("{Find(20)}")
    var Sum:int = 0
    for (X := Upto[1, 4]) { set Sum += X }
    Print("sum {Sum}")
    var Tries:int = 0
    if (X := Upto[1, 9], set Tries += 1, X > 3) then Print("x {X} tries {Tries}")

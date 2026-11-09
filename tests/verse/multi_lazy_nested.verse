# generators taken lazily, nested with each other and with choices, in fors and an if (#246)
Upto(A:int, B:int)<computes><decides>:int =
    A <= B
    A | Upto[A + 1, B]
Main():void =
    for (X := Upto[1, 2], Y := Upto[X, 3]):
        Print("{X} {Y}")
    for (Y := 1 | 2, X := Upto[Y, 2], Z := 10 | 20):
        Print("{Y} {X} {Z}")
    if (X := Upto[1, 9], Y := 1 | 2, X * Y > 7):
        Print("{X} {Y}")

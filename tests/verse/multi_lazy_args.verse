# a lazily taken call with a tuple argument, and one whose argument is another (#246): run again for each value of that one, it starts from its arguments each time
Upto(A:int, B:int)<computes><decides>:int =
    A <= B
    A | Upto[A + 1, B]
Main():void =
    P := (2, 4)
    for (X := Upto[P]) { Print("{X}") }
    for (X := Upto[1, Upto[2, 3]]) { Print("n {X}") }

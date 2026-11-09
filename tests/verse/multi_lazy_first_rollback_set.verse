# a set after a generator in option{…}, undone for the value the clauses after it reject (#246, review of #267)
Upto(A:int, B:int)<computes><decides>:int =
    A <= B
    A | Upto[A + 1, B]
Main():void =
    var T:int = 0
    O := option{X := Upto[1, 2]; set T += 1; Y := Upto[1, 2]; X + Y = 4; X}
    Print("T {T}")

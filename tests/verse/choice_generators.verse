# recursive functions with several values (#235): effect-free ones are
# computed at the call as the array of their values, in spatial order
Upto(A:int, B:int)<computes><decides>:int =
    A <= B
    A | Upto[A + 1, B]
Evens(A:int, B:int)<computes><decides>:int =
    X := Upto[A, B]
    Mod[X, 2] = 0
    X
Path(N:int)<computes>:string = if (N = 0) then "" else ("L{Path(N - 1)}" | "R{Path(N - 1)}")
Main():void =
    for (X := Upto[1, 5]) { Print("{X}") }
    if (X := Upto[1, 10], X * X > 50) then Print("first {X}")
    Es := for{Evens[1, 9]}
    Print("evens {Es.Length}")
    for (P := Path(2)) { Print(P) }
    for (X := Upto[1, 3], Y := Upto[X, 3], X + Y = 4) { Print("{X}+{Y}") }

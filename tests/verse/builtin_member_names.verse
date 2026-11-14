# A class's method may take a built-in type's member's name: a call's
# receiver says whose it is. An extension method of a built-in type may too
# when its parameters are other than the built-in's (Book of Verse ch. 6).
c := class:
    Find(X:int):int = X + 100
    ReplaceFirstElement(X:int, Y:int):int = X + Y
    ToChar():int = 7
(A:[]int).Find(X:string):int = 42
(N:int).Last():int = N - 1
Main():void =
    O := c{}
    Print("{O.Find(1)} {O.ReplaceFirstElement(1, 2)} {O.ToChar()}")
    A := array{1, 2, 3}
    if (I := A.Find[3]) then Print("built-in Find {I}")
    if (B := A.ReplaceFirstElement[2, 9], E := B[1]) then Print("built-in ReplaceFirstElement {E}")
    if (Ch := 65.ToChar[]) then Print("built-in ToChar {Ch}")
    Print("extension Find {A.Find("x")}")
    Print("extension Last {5.Last()}")
    if (L := A.Last[]) then Print("built-in Last {L}")

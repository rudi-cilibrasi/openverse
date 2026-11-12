cell := class:
    var N:int = 0
Pair(C:cell):tuple(int, int) =
    set C.N += 1
    Print("pair {C.N}")
    (10, 20)
F(X:int, Y:int):string = "two {X + Y}"
F(X:string):string = "one {X}"
Main():void =
    C := cell{}
    Print(F(Pair(C)))
    Print("state {C.N}")

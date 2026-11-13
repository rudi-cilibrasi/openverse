# suspension inside recursion, generics, if, loop, for and defer (#156)
counter := class:
    var N:int = 0
Fact(N:int)<suspends>:int =
    if (N <= 1) then return 1
    Sleep(0.1)
    N * Fact(N - 1)
Echo(X:t where t:type)<suspends>:t =
    Sleep(0.01)
    X
Pick(B:logic)<suspends>:string =
    if (B?):
        Sleep(1.0)
        "yes"
    else:
        Sleep(2.0)
        "no"
FirstOver(Limit:int)<suspends>:int =
    var I:int = 0
    loop:
        Sleep(0.25)
        set I += 1
        if (I * I > Limit) then return I
    -1
Main()<suspends>:void =
    defer:
        Print("deferred")
    Print("{Fact(5)} {Echo(7)} {Echo("s")}")
    Print("{Pick(true)} {Pick(false)}")
    Ys := for (X := 1..6, X <> 3):
        Sleep(0.1)
        X * 10
    if (Y0 := Ys[0], Y4 := Ys[4]) then Print("{Ys.Length} {Y0} {Y4}")
    C := counter{}
    for (K := 1..4):
        set C.N += Echo(K)
    Print("{C.N} {FirstOver(50)}")
    A := array{Echo(1), Echo(2), Echo(3)}
    if (A2 := A[2]) then Print("{A2}")

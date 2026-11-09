# A block's return and break where its clauses are lifted to (#283)
F(Z : int)<transacts>:int =
    for (X := block{ if (Z > 5) then return 99; Y := 1 | 2; Y }):
        Print("{X}")
    0
G(Z : int)<transacts>:int =
    if (X := block{ if (Z > 5) then return 99; Y := 1 | 2; Y > 1; Y }):
        return X
    0
Main()<transacts>:void =
    Print("{F(1)} {F(9)}")
    Print("{G(1)} {G(9)}")
    var I : int = 0
    loop:
        set I += 1
        # (break leaves the loop, not the for)
        for (X := block{ if (I > 2) then break; Y := 1 | 2; Y * I }):
            Print("{X}")
        if (I > 5) then break
    Print("done {I}")

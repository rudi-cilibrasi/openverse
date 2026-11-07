# a program's own Round and Sqrt are the ones its calls mean (#132: soft built-ins)
Round(X:int):int = X + 100
Sqrt(X:int):int = X * X
Main():void =
    Print("{Round(1)} {Sqrt(3)}")
    if (Y := Int[2.7]) then Print("{Y} {Ln(1.0)}")

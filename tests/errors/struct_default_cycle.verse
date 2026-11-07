# expect: the default of field 'X' of a depends on itself
a := struct:
    X:int = b{}.Y
b := struct:
    Y:int = a{}.X
Main():void =
    P := a{X := 1}
    Print("{P.X}")

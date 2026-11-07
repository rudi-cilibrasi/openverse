# expect: the elements of this array have different types: a and b
counted := interface:
    var Count:int = 0
named := interface:
    Name:string = "?"
a := class(counted, named):
    Extra:int = 1
b := class(named, counted):
    Other:int = 2
c := class(named):
    Z:int = 3
Main():void =
    X := a{}
    Y := b{}
    A := array{X, Y}
    A2 := array{Y, X}
    for (E : A2) { Print("{E.Name}") }
    for (E : A) { set E.Count += 1 }
    Print("{X.Count} {Y.Count}")
    N := array{X, c{}}
    for (E : N) { Print("{E.Name}") }
    T := if (X.Count > 0) then (X, 1) else (Y, 2)
    Print("{T(0).Count}")

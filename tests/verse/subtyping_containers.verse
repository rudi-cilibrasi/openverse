# subtyping (#32) through array literals with no expected type, + on
# arrays, tuples, maps and branches of containers: classes join at a
# common supertype, covariantly

shape := class<abstract>:
    Area():int
square := class(shape):
    S:int
    Area<override>():int = S * S
circle := class(shape):
    R:int
    Area<override>():int = 3 * R * R
Total(Ss:[]shape):int =
    var N:int = 0
    for (X : Ss) { set N += X.Area() }
    N
Main():void =
    # an array literal of different classes, with no expected type
    A := array{square{S := 2}, circle{R := 1}}
    Print("{Total(A)}")
    # + of arrays of different classes
    Sq := array{square{S := 1}}
    Ci := array{circle{R := 2}}
    B := Sq + Ci
    Print("{Total(B)} {B.Length}")
    var V:[]shape = Sq
    set V += Ci
    Print("{Total(V)}")
    # tuples and maps widen
    T:tuple(shape, int) = (square{S := 3}, 1)
    Print("{T(0).Area()} {T(1)}")
    M:[string]shape = map{"a" => circle{R := 1}}
    if (X := M["a"]) then Print("{X.Area()}")
    Ms:[string]square = map{"b" => square{S := 4}}
    M2:[string]shape = Ms
    if (Y := M2["b"]) then Print("{Y.Area()}")
    # branches of arrays of different classes join
    C := if (A.Length > 1) then array{square{S := 5}} else array{circle{R := 5}}
    Print("{Total(C)}")
    D := if (A.Length > 1) then (square{S := 1}, "s") else (circle{R := 1}, "c")
    Print("{D(0).Area()} {D(1)}")

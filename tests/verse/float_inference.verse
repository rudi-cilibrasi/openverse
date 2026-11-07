# floats with generic operands, Floor[X / Y] on ints, and 1e3 literals (#127 review)
Id(X:t where t:type):t = X
Last(Xs:[]t where t:type)<decides>:t = Xs[Xs.Length - 1]
Main():void =
    if (X := Floor[7/2], Y := Ceil[7 / 2]) then Print("{X} {Y}")
    Print("{-Id(2.5)} {Id(2.5) / 2.0} {2.0 / Id(2.5)} {2 * Id(1.5)} {2.0 * Id(3)}")
    Print("{Min(Id(1.0), 2.0)} {Abs(Id(-1.5))} {Max(Min(Min(1, 2), 3), Min(4, 5))}")
    Fs:[]float = array{1.5, 2.5}
    N:int = 3
    if (Y := N * Last[Fs], Z := -Last[Fs]) then Print("{Y} {Z}")
    var V:float = 1.0
    set V *= Id(3)
    Print("{V} {1e3} {2E-2} {1.5e+3}")
    if (F := Floor[7.5 / 2.0]) then Print("{F}")

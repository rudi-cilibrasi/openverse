# expect: c implements M separately for i1 and i2: call it as X.(i1:)M
i1 := interface:
    M():int
i2 := interface:
    M():int
c := class(i1, i2):
    (i1:)M<override>():int = 1
    (i2:)M<override>():int = 2
Main():void =
    X := c{}
    Print("{X.M()}")

# expect: c implements M separately for i1 and i2: call it as X.(i1:)M
i1 := interface:
    M():int
i2 := interface:
    M():int
j := class<abstract>(i1, i2):
    M<override>():int = 7
c := class(j):
    (i1:)M<override>():int = 1
Main():void =
    X:j = c{}
    Print("{X.M()}")

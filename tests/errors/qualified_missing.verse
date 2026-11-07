# expect: c must implement M (declared abstract in i2)
i1 := interface:
    M():int
i2 := interface:
    M():int
c := class(i1, i2):
    (i1:)M<override>():int = 1
Main():void = Print("x")

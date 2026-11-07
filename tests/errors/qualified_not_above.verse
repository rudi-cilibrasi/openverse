# expect: (i2:)M: i2 is not a class or interface above c
i1 := interface:
    M():int
i2 := interface:
    M():int
c := class(i1):
    (i2:)M<override>():int = 1
Main():void = Print("x")

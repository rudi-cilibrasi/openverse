# expect: 8:4: c defines (i1:)M twice
i1 := interface:
    M():int
i2 := interface:
    M():int
c := class(i1, i2):
    (i1:)M<override>():int = 1
    (i1:)M<override>():int = 2
    (i2:)M<override>():int = 3
Main():void = Print("x")

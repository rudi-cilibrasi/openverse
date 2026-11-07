# expect: (i1:)Q: i1 has no method Q
i1 := interface:
    M():int
i2 := interface:
    M():int
c := class(i1, i2):
    M<override>():int = 1
    (i1:)Q<override>():int = 1
Main():void = Print("x")

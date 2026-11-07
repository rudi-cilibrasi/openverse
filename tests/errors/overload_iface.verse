# expect: (i) and (c)
i := interface:
    M():int
c := class:
    X:int = 0
F(I:i):int = 0
F(C:c):int = 1
Main():void = Print("x")

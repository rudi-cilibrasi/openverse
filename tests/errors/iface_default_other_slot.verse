# expect: c must implement M (declared abstract in i2)
# (i1's default is not an implementation of the unrelated i2.M)
i1 := interface:
    M():int = 10
i2 := interface:
    M():int
c := class(i1, i2):
    V:int = 0
Main():void = Print("x")

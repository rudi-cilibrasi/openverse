# expect: c inherits field 'X' as a var from one parent and not from another
base := class:
    var X:int = 0
i2 := interface:
    X:int
c := class(base, i2):
    Y:int = 0
Main():void = Print("x")

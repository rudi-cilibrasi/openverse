# expect: constructor K: i is an interface
a := class:
    X:int
    Y:int = 0
b := class(a):
    Z:int = 0
i := interface:
    M():int
K<constructor>() := i:
    X := 1
Main():void = Print("x")

# expect: K sets X twice
a := class:
    X:int
    Y:int = 0
b := class(a):
    Z:int = 0
K<constructor>() := a:
    X := 1
    X := 2
Main():void = Print("x")

# expect: K: a has no field Q
a := class:
    X:int
    Y:int = 0
b := class(a):
    Z:int = 0
K<constructor>() := a:
    Q := 1
Main():void = Print("x")

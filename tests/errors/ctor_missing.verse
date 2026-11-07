# expect: K does not set X, a field of a without a default
a := class:
    X:int
    Y:int = 0
b := class(a):
    Z:int = 0
K<constructor>() := a:
    Y := 1
Main():void = Print("x")

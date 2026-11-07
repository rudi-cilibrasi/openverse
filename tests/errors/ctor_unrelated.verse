# expect: K constructs a, and KU constructs u, which is not a or a class above it
a := class:
    X:int
    Y:int = 0
b := class(a):
    Z:int = 0
u := class:
    W:int = 0
KU<constructor>() := u:
    W := 1
K<constructor>() := a:
    KU<constructor>()
Main():void = Print("x")

# expect: K sets X twice: itself, and by delegating
a := class:
    X:int
    Y:int = 0
b := class(a):
    Z:int = 0
KA<constructor>() := a:
    X := 1
K<constructor>() := b:
    X := 2
    KA<constructor>()
Main():void = Print("x")

# expect: which constructs b itself and so sets its fields: K cannot set fields too
a := class:
    X:int
    Y:int = 0
b := class(a):
    Z:int = 0
KA<constructor>() := b:
    X := 1
K<constructor>() := b:
    Z := 2
    KA<constructor>()
Main():void = Print("x")

# expect: K1 delegates to itself, through K2
a := class:
    X:int
    Y:int = 0
b := class(a):
    Z:int = 0
K1<constructor>() := a:
    K2<constructor>()
K2<constructor>() := a:
    K1<constructor>()
Main():void = Print("x")

# expect: (a) and (b)
a := class:
    X:int = 0
b := class(a):
    Y:int = 0
F(A:a):int = 0
F(B:b):int = 1
Main():void = Print("x")

# expect: c has overloads of M a call cannot tell apart, (shape) in c and (square) in c
shape := class:
    N:int = 1
square := class(shape):
    M:int = 2
c := class:
    M(X:shape):int = 0
    M(X:square):int = 1
Main():void = Print("x")

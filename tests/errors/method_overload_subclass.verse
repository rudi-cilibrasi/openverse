# expect: q has overloads of M a call cannot tell apart, (shape) in p and (square) in q
shape := class:
    N:int = 1
square := class(shape):
    M:int = 2
p := class:
    M(X:shape):int = 0
q := class(p):
    M(X:square):int = 1
    M(S:string):int = 2
Main():void = Print("x")

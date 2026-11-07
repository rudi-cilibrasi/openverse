# expect: M<override> has the parameters of no overload of M above q
shape := class:
    N:int = 1
square := class(shape):
    M:int = 2
p := class:
    M(X:shape):int = 0
    M(S:string):int = 2
q := class(p):
    M<override>(X:square):int = 1
Main():void = Print("x")

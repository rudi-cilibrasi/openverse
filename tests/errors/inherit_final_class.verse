# expect: class shape is <final>: it cannot be inherited from
shape := class<final>:
    N:int = 0
square := class(shape):
    M:int = 0
Main():void = Print("x")

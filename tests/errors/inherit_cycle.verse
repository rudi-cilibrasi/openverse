# expect: inherits from itself
a := class(b):
    N:int = 0
b := class(a):
    M:int = 0
Main():void = Print("x")

# expect: this expression can fail, but it is not in a failure context
a := class:
    X:int
    Y:int = 0
b := class(a):
    Z:int = 0
K<constructor>(N:int)<decides> := a:
    X := N
    block:
        N > 0
Main():void = Print("x")

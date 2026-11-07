# expect: unknown identifier 'Self'
a := class:
    X:int
    Y:int = 0
b := class(a):
    Z:int = 0
K<constructor>() := a:
    X := Self.Y
Main():void = Print("x")

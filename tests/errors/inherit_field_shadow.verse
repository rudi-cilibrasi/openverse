# expect: field 'N' of b has the name of an inherited field
a := class:
    N:int = 0
b := class(a):
    N:int = 1
Main():void = Print("x")

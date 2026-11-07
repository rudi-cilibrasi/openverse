# expect: has two superclasses
a := class:
    N:int = 0
b := class:
    M:int = 0
c := class(a, b):
    K:int = 0
Main():void = Print("x")

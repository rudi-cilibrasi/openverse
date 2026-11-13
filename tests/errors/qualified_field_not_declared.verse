# expect: (b:)X: b is not c, nor a class or interface above it that declares the field X
b := class:
    Y:int = 0
c := class(b):
    (b:)X:int = 1
Main():void = {}

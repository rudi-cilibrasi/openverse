# expect: qualified implementations of the overloaded method M are not supported yet
shape := class:
    N:int = 1
square := class(shape):
    M:int = 2
i := interface:
    M(X:int):int
    M(S:string):int
q := class(i):
    (i:)M<override>(X:int):int = 1
    M<override>(S:string):int = 2
Main():void = Print("x")

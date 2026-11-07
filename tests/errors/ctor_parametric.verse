# expect: constructor functions of parametric classes (box) are not supported yet
a := class:
    X:int
    Y:int = 0
b := class(a):
    Z:int = 0
box(t:type) := class:
    V:t
K<constructor>() := box:
    V := 1
Main():void = Print("x")

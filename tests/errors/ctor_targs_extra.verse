# expect: constructor K: plain takes no type arguments
box(t:type) := class:
    Value:t
plain := class:
    N:int = 0
K<constructor>() := plain(int):
    N := 1
Main():void = Print("x")

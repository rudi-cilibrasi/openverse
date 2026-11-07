# expect: expected int, found t
box(t:type) := class:
    Value:t
plain := class:
    N:int = 0
K<constructor>(V:t where t:type) := box(int):
    Value := V
Main():void = Print("x")

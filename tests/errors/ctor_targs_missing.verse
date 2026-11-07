# expect: constructor K: box takes 1 type argument(s): write box(…) after :=
box(t:type) := class:
    Value:t
plain := class:
    N:int = 0
K<constructor>(V:int) := box:
    Value := V
Main():void = Print("x")

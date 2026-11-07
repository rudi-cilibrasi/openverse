# expect: 8:4: expected t, found int
# delegate in generic with different targs (box(t) delegating to box(int) ctor)
box(t:type) := class:
    Value:t
MakeIntBox<constructor>(V:int) := box(int):
    Value := V
MakeG<constructor>(V:t where t:type) := box(t):
    MakeIntBox<constructor>(3)
Main():void =
    S := MakeG("x")
    Print("{S.Value}")

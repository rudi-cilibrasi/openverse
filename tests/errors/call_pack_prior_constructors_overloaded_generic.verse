# expect: parameters a call cannot tell apart
# overloaded generic constructors, told apart by arity

box(t:type) := class:
    Value:t
    Count:int = 0
MakeBox<constructor>(V:t where t:type) := box(t):
    Value := V
MakeBox<constructor>(V:t, N:int where t:type) := box(t):
    Value := V
    Count := N
Main():void =
    B := MakeBox(5)
    C := MakeBox("s", 3)
    Print("{B.Value} {B.Count} {C.Value} {C.Count}")

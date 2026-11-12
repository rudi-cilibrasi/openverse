# overloaded generic constructors with different type parameters, and renamed ones (#95 review)
box(t:type) := class:
    Value:t
    Count:int = 0
MakeBox<constructor>(?V:t where t:type) := box(t):
    Value := V
MakeBox<constructor>(V:t, W:u where t:type, u:type) := box(t):
    Value := V
    Count := 2
Main():void =
    B := MakeBox(?V:=5)
    C := MakeBox("s", true)
    Print("{B.Value} {B.Count} {C.Value} {C.Count}")

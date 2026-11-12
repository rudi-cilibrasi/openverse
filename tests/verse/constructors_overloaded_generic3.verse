# overloads of a generic constructor whose type parameters differ only in name
box(t:type) := class:
    Value:t
    Count:int = 0
MakeBox<constructor>(?V:u where u:type) := box(u):
    Value := V
MakeBox<constructor>(V:t, N:int where t:type) := box(t):
    Value := V
    Count := N
Main():void =
    B := MakeBox(?V:=5)
    C := MakeBox("s", 3)
    Print("{B.Value} {B.Count} {C.Value} {C.Count}")

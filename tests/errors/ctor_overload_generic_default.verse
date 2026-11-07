# expect: MakeBox leaves Other to another overload, and its default's type mentions a type parameter of MakeBox
box(t:type) := class:
    Value:t
    Other:?t = false
MakeBox<constructor>(V:t where t:type) := box(t):
    Value := V
MakeBox<constructor>(V:t, W:t where t:type) := box(t):
    Value := V
    Other := option{W}
Main():void =
    B := MakeBox(5)
    Print("{B.Value}")

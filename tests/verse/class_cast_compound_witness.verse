box(t:type) := class:
    X:t
low(u:type) := class(box(tuple(char,u))) {}
F(X:t where t:type):t =
    R:box(tuple(char,t)) = low(t){X:=('x',X)}
    if (D:=low[R]) then D.X(1) else R.X(1)
Main():void =
    Print("{F(3)}")
    Print(F("s"))

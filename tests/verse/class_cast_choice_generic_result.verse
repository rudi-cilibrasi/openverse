box(t:type) := class:
    A:t
    B:t
fixed := class(box(int)) {}
Fix(F:fixed):int = 70 | 80
Base(P:box(t) where t:type):t = P.A | P.B
Get(X:box(t) where t:type):[]t =
    for (V:t = if (F := fixed[X]) then Fix(F) else Base(X)) { V }
Main():void =
    for (V : Get(fixed{A:=3,B:=4})) { Print("{V}") }
    for (V : Get(box(string){A:="a",B:="b"})) { Print("{V}") }

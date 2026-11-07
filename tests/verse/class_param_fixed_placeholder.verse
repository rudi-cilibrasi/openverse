# regression test from the #39 review (p06b)
intcell := class(cell(int)):
    X:int = 0
cell(t:type) := class:
    Value:t
Main():void =
    C := cell(string){Value := "s"}
    Print(C.Value)

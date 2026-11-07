# regression test from the #39 review (p19_super_void)
cell(t:type) := class:
    var Value:t
    Set(X:t):void = set Value = X
counter(t:type) := class(cell(t)):
    var Count:int = 0
    Set<override>(X:t):void =
        set Count += 1
        (super:)Set(X)
Main():void =
    C := counter(int){Value := 1}
    C.Set(2)
    Print("{C.Value} {C.Count}")

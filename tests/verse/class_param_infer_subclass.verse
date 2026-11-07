# regression test from the #39 review (p04_generic_infer_fixed)
cell(t:type) := class:
    var Value:t
intcell := class(cell(int)):
    Y:int = 0
Get(C:cell(t) where t:type):t = C.Value
Main():void =
    I := intcell{Value := 4}
    Print("{Get(I)}")

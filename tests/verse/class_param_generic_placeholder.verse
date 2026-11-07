# regression test from the #39 review (p05_generic_placeholder)
cell(t:type) := class<abstract>:
    Value:t
intcell := class(cell(int)):
    X:int = 0
Get(O:?cell(t), D:t where t:type):t =
    if (C := O?) then C.Value else D
Main():void =
    O:?cell(int) = option{intcell{Value := 5}}
    Print("{Get(O, 0)}")

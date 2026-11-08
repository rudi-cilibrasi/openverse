# expect: every class below cell (intcell) fixes type arguments that cell(t) does not have, so none can be it
cell(t:type) := class<abstract>:
    Value:t
    Get():t = Value
intcell := class(cell(int)):
    Get<override>():int = Value + 1
Get(O:?cell(t), D:t where t:type):t =
    if (C := O?) then C.Get() else D
Main():void =
    O:?cell(int) = option{intcell{Value := 5}}
    Print("{Get(O, 0)}")

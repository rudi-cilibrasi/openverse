# a variable of type cell(t), when every class below cell fixes t, starts as a hidden placeholder object (#157)
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

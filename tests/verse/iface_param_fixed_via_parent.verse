# regression test from the #53 re-review (p42)
container(t:type) := interface:
    Get():t
cell(t:type) := class:
    Value:t
    Get():t = Value
intcell := class(cell(int), container(int)):
    N:int = 0
All(C:container(t) where t:type):t = C.Get()
Main():void =
    Print("{All(intcell{Value := 3}) + 1}")

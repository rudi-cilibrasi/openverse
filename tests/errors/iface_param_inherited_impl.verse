# expect: mycell uses cell.Get for container.Get, but their types differ
container(t:type) := interface:
    Get():t
cell(t:type) := class:
    Value:t
    Get():int = 42
mycell := class(cell(int), container(int)):
    N:int = 0
Main():void =
    Print("x")

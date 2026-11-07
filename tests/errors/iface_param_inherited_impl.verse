# expect: fixes, repeats or adds type arguments that container leaves open
container(t:type) := interface:
    Get():t
cell(t:type) := class:
    Value:t
    Get():int = 42
mycell := class(cell(int), container(int)):
    N:int = 0
Main():void =
    Print("x")

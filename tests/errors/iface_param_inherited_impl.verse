# expect: mycell uses cell.Get for container.Get, but their types differ
# (#724: a class implements an interface's abstract method itself, or a class
# below the interface does: a method of its name from a class that is not below
# the interface is that class's own; UEFN 43.12 error 3591,
# followup-book2/final-method-interface)
container(t:type) := interface:
    Get():t = Get()
cell(t:type) := class:
    Value:t
    Get():int = 42
mycell := class(cell(int), container(int)):
    N:int = 0
Main():void =
    Print("x")

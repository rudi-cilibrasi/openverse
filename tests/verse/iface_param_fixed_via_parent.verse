# regression test from the #53 re-review (p42)
# (#724: a class implements an interface's abstract method itself, or a class
# below the interface does: a method of its name from a class that is not below
# the interface is that class's own; UEFN 43.12 error 3591,
# followup-book2/final-method-interface)
container(t:type) := interface:
    Get():t
cell(t:type) := class:
    Value:t
    Get():t = Value
intcell := class(cell(int), container(int)):
    N:int = 0
    Get<override>():int = Value
All(C:container(t) where t:type):t = C.Get()
Main():void =
    Print("{All(intcell{Value := 3}) + 1}")

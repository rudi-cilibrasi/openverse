# expect: intcell fixes or repeats type arguments that container leaves open, so it cannot override Get
container(t:type) := interface:
    Get():t
intcell := class(container(int)):
    N:int
    Get<override>():int = N
Main():void = Print("x")

# a class that implements an interface at fixed type arguments, called from
# code generic over the interface (#142; refused before, #53)
container(t:type) := interface:
    Get():t
intcell := class(container(int)):
    N:int
    Get<override>():int = N
box(t:type) := class(container(t)):
    V:t
    Get<override>():t = V
GetC(C:container(t) where t:type):t = C.Get()
Main():void =
    Print("{GetC(intcell{N := 7})}")
    Print(GetC(box(string){V := "s"}))
    Cs:[]container(int) = array{intcell{N := 1}, box(int){V := 2}}
    for (C : Cs) { Print("{GetC(C)}") }

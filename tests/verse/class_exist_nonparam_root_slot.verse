# a variable of a non-parametric class type, whose classes below need a type
# argument a dispatch opens, starts as the class's placeholder (#209)
shape := class<abstract>:
    Area():int
box(t:type) := class(shape):
    N:int
    Area<override>():int = N
Main():void =
    S:shape = box(string){N := 5}
    Print("{S.Area()}")

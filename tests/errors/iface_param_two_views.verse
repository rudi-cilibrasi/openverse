# expect: both gives sink the type arguments u, but its own are t, u: a class below an interface that does not give it its first type parameters, in order, is not supported yet (#276)
container(t:type) := interface:
    Size():int
sink(t:type) := interface:
    Count():int
both(t:type, u:type) := class(container(t), sink(u)):
    Size<override>():int = 0
    Count<override>():int = 0
Main():void = Print("x")

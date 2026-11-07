# expect: both gives container the type arguments t, but its own are t, u
container(t:type) := interface:
    Size():int
sink(t:type) := interface:
    Count():int
both(t:type, u:type) := class(container(t), sink(u)):
    Size<override>():int = 0
    Count<override>():int = 0
Main():void = Print("x")

# expect: must give container its own type parameters
container(t:type) := interface:
    Get():t
c2(t:type) := interface(container([]t)):
    Size():int = 0
box(t:type) := class(container(t), c2(t)):
    Value:t
    Get<override>():t = Value
Main():void = Print("x")

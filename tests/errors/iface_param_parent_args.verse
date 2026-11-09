# expect: box implements container at two instances, container(t) and container([]t), through the interfaces it lists
container(t:type) := interface:
    Get():t
c2(t:type) := interface(container([]t)):
    Size():int = 0
box(t:type) := class(container(t), c2(t)):
    Value:t
    Get<override>():t = Value
Main():void = Print("x")

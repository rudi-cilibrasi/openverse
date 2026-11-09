# expect: cannot cast a container(u) to c2: c2 has type parameters that container does not have
# (an interface has no hidden fields to read a cast's opened type parameters from, #53)
container(t:type) := interface:
    Get():t
c2(t:type) := interface(container([]t)):
    Size():int
box(t:type) := class(c2(t)):
    V:t
    Get<override>():[]t = array{V, V}
    Size<override>():int = 2
TryC2(C:container(u) where u:type):int =
    if (B := c2[C]) then B.Size() else 0
Main():void =
    Print("{TryC2(box(string){V := "x"})}")

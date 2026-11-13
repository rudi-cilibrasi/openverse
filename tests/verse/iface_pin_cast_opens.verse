# (#53) a cast to an interface that gives its parent type arguments of its own
# opens them: a test of each class below both, each calling the branch's
# function at that class's (box's t, from its hidden field)
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

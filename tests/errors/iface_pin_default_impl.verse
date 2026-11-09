# expect: cannot call c2.Get here yet
# (an interface's default implementation of its parent's method, at type arguments
# the interface fixes otherwise, reached from container(u): it would need t, #53)
container(t:type) := interface:
    Get():t
c2(t:type) := interface(container([]t)):
    V():t
    Get<override>():[]t = array{V()}
box(t:type) := class(c2(t)):
    X:t
    V<override>():t = X
G(C:container(u) where u:type):u = C.Get()
Main():void = Print("{G(box(int){X := 1}).Length}")

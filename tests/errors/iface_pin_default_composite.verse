# expect: cannot call c2.Get here yet
# (tb gives c2 a composite type argument, tuple(a, b), not its own type parameters by
# name: it gets no copy of c2's default Get, whose hidden argument a dispatch from
# container(u) cannot pass; a class that gives c2 its own does, iface_default_copies)
container(t:type) := interface:
    Get():t
c2(t:type) := interface(container([]t)):
    V():t
    Get<override>():[]t = array{V()}
tb(a:type, b:type) := class(c2(tuple(a, b))):
    X:a
    Y:b
    V<override>():tuple(a, b) = (X, Y)
G(C:container(u) where u:type):u = C.Get()
Main():void = Print("{G(tb(int, int){X := 1, Y := 2}).Length}")

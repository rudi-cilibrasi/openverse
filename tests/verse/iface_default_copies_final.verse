# a <final> default of a pinned interface (#53): copied as the interface's own (the
# copy is not an override of it), so a dispatch from container(u) reaches it
container(t:type) := interface:
    Get():t
c2(t:type) := interface(container([]t)):
    V():t
    Get<override><final>():[]t = array{V(), V()}
box(a:type) := class(c2(a)):
    X:a
    V<override>():a = X
G(C:container(u) where u:type):u = C.Get()
Main():void =
    B := box(int){X := 1}
    Print("{B.Get().Length} {G(B).Length}")

# both overloads of a pinned interface's default are copied, renamed to box's a (#53)
container(t:type) := interface:
    Get():t
    Get(N:int):t
c2(t:type) := interface(container([]t)):
    V():t
    Get<override>():[]t = array{V()}
    Get<override>(N:int):[]t = for (I := 1..N) { V() }
box(a:type) := class(c2(a)):
    X:a
    V<override>():a = X
G(C:container(u) where u:type):u = C.Get()
G2(C:container(u) where u:type):u = C.Get(3)
Main():void =
    B := box(int){X := 1}
    Print("{B.Get().Length} {B.Get(3).Length} {G(B).Length} {G2(B).Length}")

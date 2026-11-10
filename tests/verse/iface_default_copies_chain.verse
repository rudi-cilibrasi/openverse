# pinned interfaces' defaults through chains (#53): box gets c3's Get, which
# overrides c2's (not c2's too); bx4 reaches c2 through c4, which gives c2 its own
container(t:type) := interface:
    Get():t
c2(t:type) := interface(container([]t)):
    V():t
    Get<override>():[]t = array{V(), V()}
c3(t:type) := interface(c2(?t)):
    Get<override>():[]?t = array{V(), V(), V()}
c4(t:type) := interface(c2(t)):
    W():int
box(t:type) := class(c3(t)):
    X:t
    V<override>():?t = option{X}
bx4(t:type) := class(c4(t)):
    X:t
    V<override>():t = X
    W<override>():int = 1
G(C:container(u) where u:type):u = C.Get()
H(C:c2(t) where t:type):int = C.Get().Length
Main():void =
    B := box(int){X := 3}
    Print("{B.Get().Length} {H(B)} {G(B).Length}")
    B4 := bx4(int){X := 3}
    Print("{B4.Get().Length} {H(B4)}")

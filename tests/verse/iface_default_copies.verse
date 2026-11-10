# a pinned interface's default implementation of its parent's method (#53):
# c2(t) := interface(container([]t))'s Get<override>, reached from code generic
# over container(u), where the dispatch opens t: each class that lists c2 giving
# it its own type parameters gets the body as its own override (copyIfaceDefaults),
# which reads t from its hidden field; inherited by a subclass, not given to a class
# that overrides Get itself; a two-parameter interface (kv) too
container(t:type) := interface:
    Get():t
    Size():int
c2(t:type) := interface(container([]t)):
    V():t
    Get<override>():[]t = array{V(), V()}
kv(k:type, v:type) := interface(container(tuple(k, v))):
    K():k
    W():v
    Get<override>():tuple(k, v) = (K(), W())
box(t:type) := class(c2(t)):
    X:t
    V<override>():t = X
    Size<override>():int = 2
bigbox(t:type, w:type) := class(box(t)):
    Wv:w
    Size<override>():int = 3
own(t:type) := class(c2(t)):
    X:t
    V<override>():t = X
    Get<override>():[]t = array{X}
    Size<override>():int = 1
pair(k:type, v:type) := class(kv(k, v)):
    A:k
    B:v
    K<override>():k = A
    W<override>():v = B
    Size<override>():int = 2
G(C:container(u) where u:type):u = C.Get()
N(C:container(u) where u:type):int = C.Size()
H(C:c2(t) where t:type):int = C.Get().Length
Main():void =
    B := box(int){X := 1}
    BB := bigbox(int, string){X := 2, Wv := "w"}
    O := own(int){X := 3}
    P := pair(string, int){A := "a", B := 4}
    Print("{G(B).Length} {G(BB).Length} {G(O).Length} {G(P)(0)} {G(P)(1)}")
    Print("{H(B)} {H(BB)} {H(O)} {N(BB)}")
    Cs:[]container([]int) = array{B, BB, O}
    Ls := for (C : Cs) { G(C).Length }
    if (A := Ls[0], A2 := Ls[1], A3 := Ls[2]) then Print("{A} {A2} {A3}")

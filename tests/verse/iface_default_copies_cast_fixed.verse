# a cast in a pinned interface's default that can never succeed at the type
# arguments a class fixes (#53): in that class's copy it fails, as the
# interface's own default's would (bx2 fixes u to string: a pair(string, int)
# is never a dup), and succeeds where the class's arguments allow it (bx3)
pair(t:type, u:type) := class:
    A:t
    B:u
dup(t:type) := class(pair(t, t)):
    C:int = 0
container(t:type) := interface:
    Get():t
c2(t:type, u:type) := interface(container([]t)):
    V():t
    R():pair(u, int)
    Get<override>():[]t =
        if (E := dup[R()]) then array{V(), V()} else array{V()}
bx2(a:type) := class(c2(a, string)):
    X:a
    V<override>():a = X
    R<override>():pair(string, int) = pair(string, int){A := "", B := 0}
bx3(a:type) := class(c2(a, int)):
    X:a
    V<override>():a = X
    R<override>():pair(int, int) = dup(int){A := 1, B := 1}
G(C:container(u) where u:type):u = C.Get()
Main():void =
    X2 := bx2(int){X := 1}
    X3 := bx3(string){X := "s"}
    Print("{X2.Get().Length} {G(X2).Length} {X3.Get().Length} {G(X3).Length}")

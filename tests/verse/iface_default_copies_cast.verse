# a refining cast in a pinned interface's default (#53, #243): each class's copy
# lifts the cast's branch into a function of its own, at its own types, apart
# from the interface's own default's (closed's) at the same place in the source
Help():int = 4
pair(t:type, u:type) := class:
    A:t
    B:u
dup(t:type) := class(pair(t, t)):
    C:int = 0
container(t:type) := interface:
    Get():t
c2(t:type) := interface(container([]t)):
    V():t
    P():pair(t, int)
    Get<override>():[]t =
        if (D := dup[P()]) then (for (I := 1..Help()) { V() }) else array{V()}
box(a:type) := class(c2(a)):
    X:a
    Q:pair(a, int)
    (box:)Help():int = 3
    V<override>():a = X
    P<override>():pair(a, int) = Q
closed := class(c2(int)):
    Q:pair(int, int)
    V<override>():int = 7
    P<override>():pair(int, int) = Q
G(C:container(u) where u:type):u = C.Get()
Main():void =
    B := box(int){X := 1, Q := dup(int){A := 1, B := 2}}
    B2 := box(string){X := "s", Q := pair(string, int){A := "s", B := 2}}
    L := closed{Q := dup(int){A := 1, B := 1}}
    Print("{B.Get().Length} {G(B).Length} {B2.Get().Length} {G(B2).Length}")
    Print("{L.Get().Length} {G(L).Length} {B.Help()}")

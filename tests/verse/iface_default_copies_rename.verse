# a pinned interface's default whose local (Y) and parameter (X) are named like
# members of the class (box's fields X and Y) (#53): renamed in the copy, which
# a shadowing would refuse there; a dispatch from container(u) reaches it
container(t:type) := interface:
    Get(N:int):t
c2(t:type) := interface(container([]t)):
    V():t
    Get<override>(X:int):[]t =
        Y := V()
        for (I := 1..X) { Y }
box(t:type) := class(c2(t)):
    X:t
    Y:int = 0
    V<override>():t = X
G(C:container(u), N:int where u:type):u = C.Get(N)
Main():void =
    B := box(int){X := 1}
    Print("{B.Get(2).Length} {G(B, 3).Length}")

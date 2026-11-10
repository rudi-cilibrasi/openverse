# A named argument's default that is a tuple holding a literal with no type
# of its own ((false, 1), (1, array{})), in a dispatch that refines type
# arguments: through a view (#351) and to a class that fixes them (#142)
container(t:type) := interface:
    Get():t
sink(u:type) := interface:
    Pt(X:u, ?K:tuple(?int, int) = (false, 1)):int
    Pa(X:u, ?K:tuple(int, []int) = (1, array{})):int
    Pb(X:u, ?K:tuple(?u, []u) = (false, array{})):int
both(t:type, u:type) := class(container(t), sink(u)):
    V:t
    Get<override>():t = V
    Pt<override>(X:u, ?K:tuple(?int, int) = (false, 1)):int = K(1)
    Pa<override>(X:u, ?K:tuple(int, []int) = (1, array{})):int = K(0) + K(1).Length
    Pb<override>(X:u, ?K:tuple(?u, []u) = (false, array{})):int = K(1).Length + 5
one(u:type) := class(sink(u)):
    Pt<override>(X:u, ?K:tuple(?int, int) = (false, 1)):int = K(1) * 10
    Pa<override>(X:u, ?K:tuple(int, []int) = (1, array{})):int = 20
    Pb<override>(X:u, ?K:tuple(?u, []u) = (false, array{})):int = 30
box(t:type) := interface:
    Pt(X:t, ?K:tuple(?int, int) = (false, 1)):int
    Pq(X:t, ?K:tuple(int, int) = (1, 2)):int
gbox(t:type) := class(box(t)):
    Pt<override>(X:t, ?K:tuple(?int, int) = (false, 1)):int = K(1)
    Pq<override>(X:t, ?K:tuple(int, int) = (1, 2)):int = K(0) + K(1)
intbox := class(box(int)):
    Pt<override>(X:int, ?K:tuple(?int, int) = (false, 7)):int = K(1) + X
    Pq<override>(X:int, ?K:tuple(int, int) = (3, 4)):int = K(0) * K(1) + X
G(B:box(x), X:x where x:type):int = B.Pt(X) + B.Pq(X)
Main():void =
    Ss:[]sink(string) = array{both(int, string){V := 1}, one(string){}}
    for (S : Ss) { Print("{S.Pt("a")} {S.Pa("a")} {S.Pb("a")} {S.Pt("a", ?K := (option{3}, 4))}") }
    Print("{G(gbox(string){}, "s")} {G(intbox{}, 10)} {G(gbox(int){}, 1)}")

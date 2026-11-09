# a generic method called through a dispatch that opens type arguments (#209),
# its own type parameter inferred at a type that mentions the caller's: in
# the dispatch's branch the caller's values are typed under the refinement
# (t as tuple(a, b) for pairE), so its hidden argument is built from the
# caller's own (t's), which the dispatch types under the refinement too
expr(t:type) := class<abstract>:
    W(X:u, ?K:?int = false where u:type):u = X
    Ws(X:u, ?Us:[]u = array{} where u:type):int = Us.Length
    Wt(X:u, ?K:int = 0 where u:type):u = X
pairE(a:type, b:type) := class(expr(tuple(a, b))):
    W<override>(X:u, ?K:?int = false where u:type):u = X
    Ws<override>(X:u, ?Us:[]u = array{} where u:type):int = Us.Length + 10
    Wt<override>(X:u, ?K:int = 0 where u:type):u = X
num := class(expr(int)):
    W<override>(X:u, ?K:?int = false where u:type):u = X
    Ws<override>(X:u, ?Us:[]u = array{} where u:type):int = Us.Length + 20
    Wt<override>(X:u, ?K:int = 0 where u:type):u = X
F1(E:expr(t), X:t where t:type):t = E.W(X)
F2(E:expr(t), X:t where t:type):int = E.Ws(X) + E.Ws(X, ?Us := array{X, X})
F3(E:expr(t), X:t where t:type):t = E.Wt(X, ?K := 2)
F4(E:expr(t), X:t where t:type):?t = E.W(option{X})
F5(E:expr(t), X:t where t:type):[]t = E.Wt(array{X, X})
# (at the caller's other type parameter, which the dispatch does not refine,
# and at a type mentioning both)
F6(E:expr(t), X:t, Y:s where t:type, s:type):tuple(t, s) = (E.W(X), E.Wt(Y))
F7(E:expr(t), X:t, Y:s where t:type, s:type):tuple(t, s) = E.W((X, Y))
Main():void =
    P := pairE(int, string){}
    Print("{F1(P, (1, "a"))(0)} {F2(P, (2, "b"))} {F3(P, (3, "c"))(1)}")
    if (O := F4(P, (4, "d"))?) then Print("{O(0)}")
    Print("{F5(P, (5, "e")).Length} {F6(P, (6, "f"), true)(0)(0)} {F7(P, (7, "g"), 8)(1)}")
    N := num{}
    Print("{F1(N, 1)} {F2(N, 2)} {F3(N, 3)} {F5(N, 5).Length} {F7(N, 7, 8)(0)}")

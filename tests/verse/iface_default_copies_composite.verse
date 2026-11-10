# a pinned interface's default reached from container(u) in classes that give the
# interface composite type arguments (#53): tb's copy has c2's t substituted by
# tuple(a, b), also in the body's typed locals (Y:t, Z:?t); arrc gives []a; a class
# giving c2 a closed type (closed, c2(int)) needs no copy and gets none
container(t:type) := interface:
    Get():t
    Size():int
c2(t:type) := interface(container([]t)):
    V():t
    Get<override>():[]t =
        Y:t = V()
        Z:?t = option{Y}
        if (W := Z?) then array{W, Y} else array{Y}
tb(a:type, b:type) := class(c2(tuple(a, b))):
    X:a
    Yb:b
    V<override>():tuple(a, b) = (X, Yb)
    Size<override>():int = 2
arrc(a:type) := class(c2([]a)):
    X:a
    V<override>():[]a = array{X, X, X}
    Size<override>():int = 3
closed := class(c2(int)):
    V<override>():int = 5
    Size<override>():int = 1
G(C:container(u) where u:type):u = C.Get()
H(C:c2(t) where t:type):int = C.Get().Length
Main():void =
    T := tb(int, string){X := 1, Yb := "b"}
    R := G(T)
    if (F := R[0]) then Print("{R.Length} {F(0)} {F(1)} {H(T)}")
    A := arrc(int){X := 4}
    RA := G(A)
    if (F := RA[0]) then Print("{RA.Length} {F.Length} {H(A)}")
    C := closed{}
    Print("{G(C).Length} {H(C)}")

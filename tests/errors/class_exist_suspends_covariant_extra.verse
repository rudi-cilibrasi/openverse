# expect: a <suspends> override cannot be called yet through a dispatch that opens its class's type parameters when the call expects the method's result as a class above it declares it
# (midX has a type parameter, s, that expr does not: a cell of expr's classes at
# midX's type arguments has no type the refinement makes the frame's;
# without s, class_exist_suspends_covariant_mid runs)
expr(t:type) := class<abstract>:
    Eval()<suspends>:t
    Copy()<suspends>:expr(t)
midX(t:type, s:type) := class<abstract>(expr(t)):
    Copy<override>()<suspends>:midX(t, s)
pairX(a:type, b:type) := class(midX(tuple(a, b), int)):
    A:a
    B:b
    Eval<override>()<suspends>:tuple(a, b) = (A, B)
    Copy<override>()<suspends>:pairX(a, b) =
        Sleep(0.1)
        pairX(a, b){A := A, B := B}
GoX(E:midX(t, s) where t:type, s:type)<suspends>:t = E.Copy().Eval()
Main()<suspends>:void =
    Y := GoX(pairX(int, int){A := 1, B := 2})
    Print("{Y(0)}")

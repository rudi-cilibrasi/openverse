# opened <suspends> overrides called from a class between the override and
# the method's first declaration that declares the method with a narrower
# result (#209): the frame's cell holds the first declaration's result
# (expr(tuple(a, b))); a caller from mid(t) or mid2(t), whose type arguments
# are the first declaration's class's, makes its cell of expr's classes at its
# own type arguments, and narrows the value with a cast that the override's
# result always passes (Depth, of mid, reads the narrowed value)
expr(t:type) := class<abstract>:
    Eval()<suspends>:t
    Copy()<suspends>:expr(t)
mid(t:type) := class<abstract>(expr(t)):
    Copy<override>()<suspends>:mid(t)
    Depth():int = 1
mid2(t:type) := class<abstract>(mid(t)):
    Copy<override>()<suspends>:mid2(t)
    Depth<override>():int = 2
pairM(a:type, b:type) := class(mid2(tuple(a, b))):
    A:a
    B:b
    Eval<override>()<suspends>:tuple(a, b) = (A, B)
    Copy<override>()<suspends>:pairM(a, b) =
        Sleep(0.1)
        pairM(a, b){A := A, B := B}
    Depth<override>():int = 3
GoE(E:expr(t) where t:type)<suspends>:t = E.Copy().Eval()
GoM(E:mid(t) where t:type)<suspends>:int = E.Copy().Depth()
GoM2(E:mid2(t) where t:type)<suspends>:tuple(t, int) =
    C := E.Copy()
    (C.Eval(), C.Depth())
Main()<suspends>:void =
    P := pairM(int, string){A := 1, B := "b"}
    X := GoE(P)
    Print("{X(0)} {X(1)} {GoM(P)} {GoM2(P)(1)}")
    T := spawn{GoM(P)}
    Print("{T.Await()}")
    W := race:
        GoM2(P)(1)
        block:
            Sleep(10.0)
            0
    Print("{W}")

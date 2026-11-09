# a concurrent GADT evaluator: an override of a class with type parameters its
# parent's type arguments do not give spawns its subexpressions' evaluations,
# dispatches at those (opened) type parameters, and awaits them (#209): each
# spawned dispatch is a generic `$dispatchK`, a root at the override's type
# arguments (#244), given their values from the receiver
expr(t:type) := class<abstract>:
    Eval()<suspends>:t
num := class(expr(int)):
    V:int
    D:float
    Eval<override>()<suspends>:int =
        Sleep(D)
        Print("num {V}")
        V
pairE(a:type, b:type) := class(expr(tuple(a, b))):
    L:expr(a)
    R:expr(b)
    Eval<override>()<suspends>:tuple(a, b) =
        TL := spawn{L.Eval()}
        TR := spawn{R.Eval()}
        X := TL.Await()
        Y := TR.Await()
        (X, Y)
slow := class(expr(int)):
    Eval<override>()<suspends>:int =
        defer:
            Print("slow unwound")
        Sleep(10.0)
        0
Run(E:expr(t) where t:type)<suspends>:t = E.Eval()
Main()<suspends>:void =
    P := pairE(int, int){L := num{V := 1, D := 0.3}, R := num{V := 2, D := 0.1}}
    R := Run(P)
    Print("{R(0)} {R(1)}")
    Q := pairE(tuple(int, int), int){L := P, R := num{V := 3, D := 0.2}}
    S := Run(Q)
    Print("{S(0)(0)} {S(0)(1)} {S(1)}")
    T := spawn{Run(pairE(int, int){L := slow{}, R := num{V := 4, D := 0.1}})}
    Sleep(0.5)
    T.Cancel()
    Print("cancelled")

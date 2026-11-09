# expect: a <suspends> override cannot be called yet through a dispatch that opens its class's type parameters from a class that overrides its method with a narrower result than the method's first declaration's (#209)
# (the frame's result cell holds Copy's first declared result, expr(t), at
# pairM's type arguments; a call from mid expects mid(t), and the cell's type
# is invariant. The same call from expr(t) runs: class_exist_suspends_covariant)
expr(t:type) := class<abstract>:
    Eval()<suspends>:t
    Copy()<suspends>:expr(t)
mid(t:type) := class<abstract>(expr(t)):
    Copy<override>()<suspends>:mid(t)
pairM(a:type, b:type) := class(mid(tuple(a, b))):
    A:a
    B:b
    Eval<override>()<suspends>:tuple(a, b) = (A, B)
    Copy<override>()<suspends>:pairM(a, b) =
        Sleep(0.1)
        pairM(a, b){A := A, B := B}
GoM(E:mid(t) where t:type)<suspends>:t = E.Copy().Eval()
Main()<suspends>:void =
    Y := GoM(pairM(int, int){A := 1, B := 2})
    Print("{Y(0)} {Y(1)}")

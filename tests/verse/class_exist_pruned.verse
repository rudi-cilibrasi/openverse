# a generic <suspends> function dispatching on expr(t), copied at closed
# types (#225): the tests no object can pass are dropped, as the checker
# opens the type arguments of the classes tested (#209)
expr(t:type) := class<abstract>:
    Eval():t
lit := class(expr(int)):
    V:int
    Eval<override>():int = V
pairE(a:type, b:type) := class(expr(tuple(a, b))):
    L:expr(a)
    R:expr(b)
    Eval<override>():tuple(a, b) = (L.Eval(), R.Eval())
RunS(E:expr(t) where t:type)<suspends>:t =
    Sleep(0.0)
    E.Eval()
Main()<suspends>:void =
    Print("{RunS(lit{V := 1})}")

# a generic <suspends> function dispatching on expr(t), called at closed
# types: generic, its dispatch opens the type arguments of the classes
# tested (#209); copies at closed types drop the tests no object can pass
# (generic_roots_pruned.verse)
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

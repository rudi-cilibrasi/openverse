# expect: a <suspends> override whose result type is narrower than the method's it overrides cannot be called yet through a dispatch that opens its class's type parameters (#251)
expr(t:type) := class<abstract>:
    Eval()<suspends>:t
    Copy()<suspends>:expr(t)
num := class(expr(int)):
    V:int
    Eval<override>()<suspends>:int = V
    Copy<override>()<suspends>:expr(int) = num{V := V}
pairE(a:type, b:type) := class(expr(tuple(a, b))):
    L:expr(a)
    R:expr(b)
    Eval<override>()<suspends>:tuple(a, b) = (L.Eval(), R.Eval())
    Copy<override>()<suspends>:pairE(a, b) =
        Sleep(0.1)
        pairE(a, b){L := L.Copy(), R := R.Copy()}
Go(E:expr(t) where t:type)<suspends>:t = E.Copy().Eval()
Main()<suspends>:void =
    P := Go(pairE(int, int){L := num{V := 1}, R := num{V := 2}})
    Print("{P(0)} {P(1)}")

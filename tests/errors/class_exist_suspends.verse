# expect: Eval is a <suspends> override, and its class has type parameters that its parent's type arguments do not give
expr(t:type) := class<abstract>:
    Eval()<suspends>:t
pairE(a:type, b:type) := class(expr(tuple(a, b))):
    L:expr(a)
    R:expr(b)
    Eval<override>()<suspends>:tuple(a, b) = (L.Eval(), R.Eval())
Main():void = Print("x")

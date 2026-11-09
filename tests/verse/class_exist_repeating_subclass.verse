# a class below an existential one that repeats its type arguments (#209)
expr(t:type) := class<abstract>:
    Eval():t
lit := class(expr(int)):
    V:int
    Eval<override>():int = V
pairE(a:type, b:type) := class(expr(tuple(a, b))):
    L:expr(a)
    R:expr(b)
    Eval<override>():tuple(a, b) = (L.Eval(), R.Eval())
dupP(a:type) := class(pairE(a, a)):
    N:int = 0
Main():void =
    E:expr(tuple(int, int)) = pairE(int, int){L := lit{V := 1}, R := lit{V := 2}}
    Print("{E.Eval()(1)}")

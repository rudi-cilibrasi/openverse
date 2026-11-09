# expect: a class below an interface with type parameters of its own is not supported yet
expr(t:type) := interface:
    Eval():t
lit := class(expr(int)):
    V:int
    Eval<override>():int = V
pairE(a:type, b:type) := class(expr(tuple(a, b))):
    L:expr(a)
    R:expr(b)
    Eval<override>():tuple(a, b) = (L.Eval(), R.Eval())
Run(E:expr(t) where t:type):t = E.Eval()
Main():void =
    Print("{Run(pairE(int, int){L := lit{V := 1}, R := lit{V := 2}})(1)}")

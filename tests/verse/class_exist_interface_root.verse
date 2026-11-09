# a GADT through an interface (#276): expr(t) is an interface, and pairE's
# a and b, which only occur inside the type argument it gives expr, are
# opened by a dispatch from expr(t)
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

# expect: its type arguments there relate to ones that fstE does not have
expr(t:type) := class<abstract>:
    Eval():t
    Name():string = "expr"
lit := class(expr(int)):
    V:int
    Eval<override>():int = V
fstE(a:type, b:type) := class(expr(a)):
    P:expr(tuple(a, b))
    Eval<override>():a = P.Eval()(0)
fstT(a:type, b:type, c:type) := class(fstE(a, tuple(b, c))):
    Name<override>():string = "fstT"
Run(E:expr(t) where t:type):t = E.Eval()
Main():void =
    One := lit{V := 1}
    P := pairE(int, tuple(int, int)){L := One, R := pairE(int, int){L := One, R := One}}
    F := fstT(int, int, int){P := P}
    Print("{Run(F)} {F.Name()}")
pairE(a:type, b:type) := class(expr(tuple(a, b))):
    L:expr(a)
    R:expr(b)
    Eval<override>():tuple(a, b) = (L.Eval(), R.Eval())

# an abstract class with type parameters of its own, whose classes below
# have different pins past its arguments: each is tested apart (#209)
expr(t:type) := class<abstract>:
    Eval():t
    Name():string = "expr"
lit := class(expr(int)):
    V:int
    Eval<override>():int = V
pairE(a:type, b:type) := class<abstract>(expr(tuple(a, b))):
    L:expr(a)
    R:expr(b)
    Eval<override>():tuple(a, b) = (L.Eval(), R.Eval())
tagged(a:type, b:type, n:type) := class(pairE(a, b)):
    T:n
tagI(a:type, b:type) := class(tagged(a, b, int)):
    Q:int = 0
Run(E:expr(t) where t:type):t = E.Eval()
Main():void =
    One := lit{V := 1}
    T := tagged(int, int, string){L := One, R := One, T := "t"}
    I := tagI(int, int){L := One, R := lit{V := 2}, T := 3}
    Print("{Run(T)(0)} {Run(I)(1)}")

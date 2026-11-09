# a <suspends> method dispatched to a class whose pins relate the receiver's
# type arguments to ones the implementing class does not have (#209), also
# spawned and raced
expr(t:type) := class<abstract>:
    Eval()<suspends>:t
    Name():string = "expr"
lit := class(expr(int)):
    V:int
    Eval<override>()<suspends>:int =
        Sleep(0.1)
        V
pairE(a:type, b:type) := class(expr(tuple(a, b))):
    L:expr(a)
    R:expr(b)
    Eval<override>()<suspends>:tuple(a, b) = (L.Eval(), R.Eval())
fstE(a:type, b:type) := class(expr(a)):
    P:expr(tuple(a, b))
    Eval<override>()<suspends>:a =
        Sleep(0.1)
        P.Eval()(0)
fstT(a:type, b:type, c:type) := class(fstE(a, tuple(b, c))):
    Name<override>():string = "fstT"
Run(E:expr(t) where t:type)<suspends>:t = E.Eval()
Main()<suspends>:void =
    One := lit{V := 1}
    P := pairE(int, tuple(int, int)){L := lit{V := 4}, R := pairE(int, int){L := One, R := One}}
    F := fstT(int, int, int){P := P}
    Print("{Run(F)} {F.Name()}")
    T := spawn{Run(F)}
    Print("{T.Await()}")
    W := race:
        Run(F)
        block:
            Sleep(10.0)
            0
    Print("{W}")

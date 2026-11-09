# more dispatches to classes whose pins relate the receiver's type arguments
# to ones the implementing class does not have (#209): generic methods, an
# untyped named default, a composite pin (fstT2), the hidden parameter b
expr(t:type) := class<abstract>:
    Eval():t
    Name():string = "expr"
    Both(X:u where u:type):tuple(t, u)
    Pick(?Alt:?t = false):t
lit := class(expr(int)):
    V:int
    Eval<override>():int = V
    Both<override>(X:u where u:type):tuple(int, u) = (V, X)
    Pick<override>(?Alt:?int = false):int = if (A := Alt?) then A else V
pairE(a:type, b:type) := class(expr(tuple(a, b))):
    L:expr(a)
    R:expr(b)
    Eval<override>():tuple(a, b) = (L.Eval(), R.Eval())
    Both<override>(X:u where u:type):tuple(tuple(a, b), u) = (Eval(), X)
    Pick<override>(?Alt:?tuple(a, b) = false):tuple(a, b) = if (A := Alt?) then A else Eval()
fstE(a:type, b:type) := class(expr(a)):
    P:expr(tuple(a, b))
    Eval<override>():a = P.Eval()(0)
    Both<override>(X:u where u:type):tuple(a, u) = (Eval(), X)
    Pick<override>(?Alt:?a = false):a = if (A := Alt?) then A else Eval()
    Snd():b = P.Eval()(1)
fstT(a:type, b:type, c:type) := class(fstE(a, tuple(b, c))):
    Name<override>():string = "fstT"
fstT2(a:type, b:type, c:type) := class(fstE(tuple(a, b), c)):
    Name<override>():string = "fstT2"
Run(E:expr(t) where t:type):t = E.Eval()
RunB(E:expr(t), X:s where t:type, s:type):tuple(t, s) = E.Both(X)
RunP(E:expr(t) where t:type):t = E.Pick()
RunP2(E:expr(t), X:t where t:type):t = E.Pick(?Alt := option{X})
Main():void =
    One := lit{V := 1}
    P := pairE(int, tuple(int, int)){L := One, R := pairE(int, int){L := One, R := lit{V := 5}}}
    F := fstT(int, int, int){P := P}
    Print("{Run(F)} {F.Name()} {RunB(F, "x")(1)} {RunP(F)} {RunP2(F, 9)} {F.Snd()(1)}")
    G := fstT2(int, int, string){P := pairE(tuple(int, int), string){L := pairE(int, int){L := One, R := lit{V := 2}}, R := strE{}}}
    Print("{Run(G)(1)} {G.Name()} {RunB(G, 3)(1)} {RunP(G)(0)}")
strE := class(expr(string)):
    Eval<override>():string = "s"
    Both<override>(X:u where u:type):tuple(string, u) = ("s", X)
    Pick<override>(?Alt:?string = false):string = "s"
S1:strE = strE{}

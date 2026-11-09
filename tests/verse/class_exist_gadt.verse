# a GADT evaluator (#209): pairE's type parameters are given only inside the
# type argument it gives expr, and fstE's b not at all; a dispatch on an
# expr(t) opens them, and their methods take values of them (for their
# slots) from hidden fields of the object
expr(t:type) := class<abstract>:
    Eval():t
    Describe():string = "expr"
lit := class(expr(int)):
    V:int
    Eval<override>():int = V
    Describe<override>():string = "lit {V}"
add := class(expr(int)):
    L:expr(int)
    R:expr(int)
    Eval<override>():int = L.Eval() + R.Eval()
iszero := class(expr(logic)):
    E:expr(int)
    Eval<override>():logic = logic{E.Eval() = 0}
cond(t:type) := class(expr(t)):
    C:expr(logic)
    T:expr(t)
    F:expr(t)
    Eval<override>():t = if (C.Eval()?) then T.Eval() else F.Eval()
pairE(a:type, b:type) := class(expr(tuple(a, b))):
    L:expr(a)
    R:expr(b)
    Eval<override>():tuple(a, b) =
        var X:a = L.Eval()
        Y:b = R.Eval()
        set X = L.Eval()
        (X, Y)
    Describe<override>():string = "pair of {L.Describe()} and {R.Describe()}"
fstE(a:type, b:type) := class(expr(a)):
    P:expr(tuple(a, b))
    Eval<override>():a = P.Eval()(0)
sndE(a:type, b:type) := class(expr(b)):
    P:expr(tuple(a, b))
    Eval<override>():b = P.Eval()(1)
# a class below pairE with a type parameter of its own too
tagged(a:type, b:type, n:type) := class(pairE(a, b)):
    Tag:n
    Describe<override>():string = "tagged {(super:)Describe()}"
Run(E:expr(t) where t:type):t = E.Eval()
Main():void =
    One := lit{V := 1}
    Two := add{L := lit{V := 2}, R := lit{V := 0}}
    P := pairE(int, logic){L := Two, R := iszero{E := lit{V := 0}}}
    R := Run(P)
    Print("{R(0)} {if (R(1)?) then "true" else "false"}")
    Print("{Run(fstE(int, logic){P := P})}")
    Print(if (Run(sndE(int, logic){P := P})?) then "snd true" else "snd false")
    Print("{Run(cond(int){C := iszero{E := One}, T := One, F := Two})}")
    Q := tagged(int, int, string){L := One, R := Two, Tag := "q"}
    S := Run(Q)
    Print("{S(0)} {S(1)}")
    Es:[]expr(tuple(int, int)) = array{Q, pairE(int, int){L := Two, R := One}}
    for (E : Es) { Print("{E.Describe()}: {Run(E)(0)}") }

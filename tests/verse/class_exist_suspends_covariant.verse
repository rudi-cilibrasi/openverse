# <suspends> overrides with narrower (covariant) results, in classes with type
# parameters that their parent's type arguments do not give (#209): a
# dispatch from expr(t) opens them, and the caller reads the result from a
# cell of its own type. The frame's cell holds the method's declared result
# (expr(tuple(a, b)) for pairE's Copy), so the override writes its narrower
# pairE(a, b) there by subsumption.
expr(t:type) := class<abstract>:
    Eval()<suspends>:t
    Copy()<suspends>:expr(t)
    Lift(X:u where u:type)<suspends>:holder(u)
holder(u:type) := class:
    H:u
    Show():string = "holder"
tagged(u:type) := class(holder(u)):
    Tag:int
    Show<override>():string = "tagged {Tag}"
num := class(expr(int)):
    V:int
    Eval<override>()<suspends>:int = V
    Copy<override>()<suspends>:num =
        Sleep(0.1)
        num{V := V + 10}
    Lift<override>(X:u where u:type)<suspends>:holder(u) = holder(u){H := X}
pairE(a:type, b:type) := class(expr(tuple(a, b))):
    L:expr(a)
    R:expr(b)
    Eval<override>()<suspends>:tuple(a, b) = (L.Eval(), R.Eval())
    # (narrower than expr(tuple(a, b)), and it suspends twice, once in each
    # nested call, also at opened types)
    Copy<override>()<suspends>:pairE(a, b) =
        Sleep(0.1)
        pairE(a, b){L := L.Copy(), R := R.Copy()}
    # (the method's own type parameter, renamed apart from the class's)
    Lift<override>(X:u where u:type)<suspends>:tagged(u) =
        Sleep(0.1)
        tagged(u){H := X, Tag := 2}
# (a class whose type parameter its parent's type arguments do not mention)
hidE(a:type) := class(expr(int)):
    W:a
    K:int
    Eval<override>()<suspends>:int = K
    Copy<override>()<suspends>:hidE(a) =
        Sleep(0.1)
        hidE(a){W := W, K := K * 2}
    Lift<override>(X:u where u:type)<suspends>:tagged(u) = tagged(u){H := X, Tag := K}
Go(E:expr(t) where t:type)<suspends>:t = E.Copy().Eval()
Twice(E:expr(t) where t:type)<suspends>:expr(t) = E.Copy().Copy()
Shown(E:expr(t) where t:type)<suspends>:string = E.Lift("x").Show()
Main()<suspends>:void =
    P := pairE(int, int){L := num{V := 1}, R := num{V := 2}}
    X := Go(P)
    Print("{X(0)} {X(1)}")
    Q := pairE(tuple(int, int), int){L := P, R := hidE(string){W := "w", K := 3}}
    Y := Twice(Q).Eval()
    Print("{Y(0)(0)} {Y(0)(1)} {Y(1)}")
    Print("{Shown(P)} {Shown(num{V := 0})} {Shown(hidE(logic){W := true, K := 7})}")
    # (spawned: the dispatch is lifted into a generic call, a root at its
    # type arguments)
    T := spawn{Go(Q)}
    Z := T.Await()
    Print("{Z(0)(0)} {Z(0)(1)} {Z(1)}")
    # (in a race, the loser cancelled at its next suspension)
    W := race:
        Go(P)
        block:
            Sleep(10.0)
            (0, 0)
    Print("{W(0)} {W(1)}")

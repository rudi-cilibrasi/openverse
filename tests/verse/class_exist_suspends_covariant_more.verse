# opened <suspends> overrides whose result cell keeps the override's own
# result (#209): a class above it that a dispatch opens from declares the
# method with that result, and calls from there worked before narrower
# results did; and qualified implementations, whose roots are above their
# qualifier (shapes from the review)
# (an interface root, a class between that declares Copy narrower, and the
# override at that class's result, called from code generic over the class)
copierA(t:type) := interface:
    Copy()<suspends>:copierA(t)
exprA(t:type) := class<abstract>(copierA(t)):
    Eval()<suspends>:t
    Copy<override>()<suspends>:exprA(t)
pairA(a:type, b:type) := class(exprA(tuple(a, b))):
    A:a
    B:b
    Eval<override>()<suspends>:tuple(a, b) = (A, B)
    Copy<override>()<suspends>:exprA(tuple(a, b)) =
        Sleep(0.1)
        pairA(a, b){A := A, B := B}
GoA(E:exprA(t) where t:type)<suspends>:t = E.Copy().Eval()
# (the same with the method's own type parameter)
holder(u:type) := class:
    H:u
    Sh():string = "holder"
tagged(u:type) := class(holder(u)):
    Tg:int
    Sh<override>():string = "tagged {Tg}"
exprH(t:type) := class<abstract>:
    Lift(X:u where u:type)<suspends>:holder(u)
midH(t:type) := class<abstract>(exprH(t)):
    Lift<override>(X:v where v:type)<suspends>:tagged(v)
pairH(a:type, b:type) := class(midH(tuple(a, b))):
    A:a
    Lift<override>(X:u where u:type)<suspends>:tagged(u) =
        Sleep(0.1)
        tagged(u){H := X, Tg := 5}
ShH(E:midH(t) where t:type)<suspends>:string = E.Lift(1).Sh()
# (two roots, implemented by qualified overrides, each narrower than its root)
exprQ(t:type) := class<abstract>:
    Copy()<suspends>:exprQ(t)
    Eval()<suspends>:t
copierQ(t:type) := interface:
    Copy()<suspends>:copierQ(t)
pairQ(a:type, b:type) := class(exprQ(tuple(a, b)), copierQ(tuple(a, b))):
    A:a
    B:b
    Eval<override>()<suspends>:tuple(a, b) = (A, B)
    (exprQ:)Copy<override>()<suspends>:pairQ(a, b) =
        Sleep(0.1)
        pairQ(a, b){A := A, B := B}
    (copierQ:)Copy<override>()<suspends>:pairQ(a, b) =
        Sleep(0.1)
        pairQ(a, b){A := A, B := B}
GoQ(E:exprQ(t) where t:type)<suspends>:t = E.Copy().Eval()
GoC(E:copierQ(tuple(int, int)))<suspends>:void =
    X := E.Copy()
    Print("copied")
Main()<suspends>:void =
    Y := GoA(pairA(int, int){A := 1, B := 2})
    Print("{Y(0)} {Y(1)}")
    Print(ShH(pairH(int, string){A := 1}))
    P := pairQ(int, int){A := 3, B := 4}
    Z := GoQ(P)
    Print("{Z(0)} {Z(1)}")
    GoC(P)

# more opened <suspends> overrides below a class that redeclares the method
# narrower (#209, shapes from the review of #337):
# (the override returns exactly mid's declared result, so its frame's cell
# keeps that, mid(tuple(a, b)); a caller from expr(t) makes its cell of mid's
# classes at its own type arguments and reads it with no cast)
expr(t:type) := class<abstract>:
    Copy()<suspends>:expr(t)
    Name():string = "e"
mid(t:type) := class<abstract>(expr(t)):
    Copy<override>()<suspends>:mid(t)
    Depth():int = 1
pairM(a:type, b:type) := class(mid(tuple(a, b))):
    A:a
    Copy<override>()<suspends>:mid(tuple(a, b)) =
        Sleep(0.1)
        pairM(a, b){A := A}
    Depth<override>():int = 3
GoM(E:mid(t) where t:type)<suspends>:int = E.Copy().Depth()
GoE(E:expr(t) where t:type)<suspends>:string = E.Copy().Name()
# (the override's result is a class with a type parameter its parent's type
# arguments do not give, later(tuple(a, b), b): more type arguments than the
# cell's type, so the cell starts as a default of its own type)
exprL(t:type) := class<abstract>:
    Copy()<suspends>:exprL(t)
midL(t:type) := class<abstract>(exprL(t)):
    Copy<override>()<suspends>:midL(t)
    Depth():int = 1
later(t:type, s:type) := class(midL(t)):
    V:int
    Copy<override>()<suspends>:later(t, s) = later(t, s){V := V}
    Depth<override>():int = V
pairL(a:type, b:type) := class(midL(tuple(a, b))):
    A:a
    Copy<override>()<suspends>:later(tuple(a, b), b) =
        Sleep(0.1)
        later(tuple(a, b), b){V := 7}
    Depth<override>():int = 3
GoL(E:midL(t) where t:type)<suspends>:int = E.Copy().Depth()
GoLE(E:exprL(t) where t:type)<suspends>:int =
    C := E.Copy()
    0
Main()<suspends>:void =
    P := pairM(int, int){A := 1}
    Print("{GoM(P)} {GoE(P)}")
    Q := pairL(int, int){A := 1}
    Print("{GoL(Q)} {GoL(later(int, string){V := 4})} {GoLE(Q)}")

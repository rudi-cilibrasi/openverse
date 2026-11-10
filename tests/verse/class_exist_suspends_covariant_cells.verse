# an opened <suspends> override called from classes that declare the method with
# results no one cell serves (#209): expr(t)'s expr(t), midX(t, s)'s midX(t, s)
# (a type parameter expr does not have) and copier(t)'s copier(t) (another root):
# its frame keeps a cell for each, writes its result to every one, and each
# caller passes the one its class's declaration gives; spawned and raced
expr(t:type) := class<abstract>:
    Eval()<suspends>:t
    Copy()<suspends>:expr(t)
copier(t:type) := interface:
    Copy()<suspends>:copier(t)
    Tag():int
midX(t:type, s:type) := class<abstract>(expr(t), copier(t)):
    Copy<override>()<suspends>:midX(t, s)
    Extra():int = 1
pairX(a:type, b:type) := class(midX(tuple(a, b), int)):
    A:a
    B:b
    Eval<override>()<suspends>:tuple(a, b) = (A, B)
    Copy<override>()<suspends>:pairX(a, b) =
        Sleep(0.1)
        pairX(a, b){A := A, B := B}
    Tag<override>():int = 7
    Extra<override>():int = 9
GoE(E:expr(t) where t:type)<suspends>:t = E.Copy().Eval()
GoX(E:midX(t, s) where t:type, s:type)<suspends>:int = E.Copy().Extra()
GoC(E:copier(t) where t:type)<suspends>:int = E.Copy().Tag()
Main()<suspends>:void =
    P := pairX(int, string){A := 1, B := "b"}
    Y := GoE(P)
    Print("{Y(0)} {Y(1)} {GoX(P)} {GoC(P)}")
    T := spawn{GoX(P)}
    Print("{T.Await()}")
    W := race:
        GoC(P)
        block:
            Sleep(10.0)
            0
    Print("{W}")

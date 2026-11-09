# untyped named defaults through opening dispatches (#209): a <suspends>
# method (also spawned), an interface, and a generic method whose own type
# parameter the call infers
expr(t:type) := class<abstract>:
    Eval()<suspends>:t
    Pick(?Alt:?t = false)<suspends>:t =
        if (A := Alt?) then A else Eval()
    Wrap(X:u, ?Alt:?u = false where u:type):u = X
pairE(a:type, b:type) := class(expr(tuple(a, b))):
    A:a
    B:b
    Eval<override>()<suspends>:tuple(a, b) =
        Sleep(0.1)
        (A, B)
    Pick<override>(?Alt:?tuple(a, b) = false)<suspends>:tuple(a, b) =
        Sleep(0.1)
        if (X := Alt?) then X else (A, B)
    Wrap<override>(X:u, ?Alt:?u = false where u:type):u = if (Y := Alt?) then Y else X
Run0(E:expr(t) where t:type)<suspends>:t = E.Pick()
Go(E:expr(t) where t:type):int = E.Wrap(3)

shower(t:type) := interface:
    Show(?Pre:[]t = array{}):string
box(t:type) := class(shower(t)):
    V:t
    Show<override>(?Pre:[]t = array{}):string = "box {Pre.Length}"
pairB(a:type, b:type) := class(shower(tuple(a, b))):
    A:a
    Show<override>(?Pre:[]tuple(a, b) = array{}):string = "pair {Pre.Length}"
Show2(S:shower(t) where t:type):string = S.Show()

Main()<suspends>:void =
    P := pairE(int, string){A := 1, B := "b"}
    Print("{Run0(P)(1)}")
    T := spawn{Run0(P)}
    Print("{T.Await()(0)}")
    Print("{Go(pairE(int, int){A := 1, B := 2})}")
    Print(Show2(box(int){V := 1}))
    Print(Show2(pairB(int, string){A := 2}))

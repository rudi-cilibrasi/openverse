# opened <suspends> overrides (#251) with a branch and a sync, calling a
# generic suspends function, one with a type parameter of its own, and one
# called directly at closed types
job(t:type) := class<abstract>:
    Run()<suspends>:t
    With(X:u where u:type)<suspends>:tuple(t, u)
lit := class(job(int)):
    V:int
    Run<override>()<suspends>:int =
        Sleep(0.1)
        V
    With<override>(X:u where u:type)<suspends>:tuple(int, u) =
        Sleep(0.1)
        (V, X)
Pause(X:t where t:type)<suspends>:t =
    Sleep(0.05)
    X
boxJ(a:type, b:type) := class(job(a)):
    L:job(a)
    B:b
    Run<override>()<suspends>:a =
        branch:
            Sleep(0.05)
            Print("branch ran")
        S := sync:
            L.Run()
            Pause(B)
        Pause(S(0))
    With<override>(X:u where u:type)<suspends>:tuple(a, u) =
        P := L.With(B)
        (P(0), X)
Go(J:job(t) where t:type)<suspends>:t = J.Run()
GoW(J:job(t) where t:type)<suspends>:tuple(t, string) = J.With("w")
Main()<suspends>:void =
    J := boxJ(int, string){L := lit{V := 1}, B := "b"}
    Print("{Go(J)}")
    W := GoW(J)
    Print("{W(0)} {W(1)}")
    Print("direct {J.Run()}")
    K := boxJ(int, logic){L := J, B := true}
    Print("{Go(K)}")

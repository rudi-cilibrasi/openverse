# branch, rush and spawn in generic functions, which are specialised at the
# types they are used at (#174)
Tick(Name:string, X:t where t:type)<suspends>:t =
    Sleep(1.0)
    Print("tick {Name}")
    X
Watch(X:t, Name:string where t:type)<suspends>:t =
    branch:
        loop:
            Sleep(0.5)
            Print("watching {Name}")
    Sleep(1.2)
    X
First(A:t, B:t where t:type)<suspends>:t =
    rush:
        Tick("a", A)
        block:
            Sleep(2.0)
            Print("b done")
            B
Later(X:t where t:type)<suspends>:task(t) =
    spawn{Tick("later", X)}
Main()<suspends>:void =
    Print("{Watch(5, "int")}")
    Print("{Watch("s", "str")}")
    Print("{First(1, 2)}")
    T := Later(array{1, 2})
    Print("{T.Await().Length}")
    U := Later("u")
    Print("{U.Await()}")
    Sleep(2.0)

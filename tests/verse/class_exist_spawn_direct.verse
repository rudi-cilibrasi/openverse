# a spawn of a call of a method of a class with type parameters that its
# parent's type arguments do not give (#209): the method reads those from its
# receiver and takes hidden arguments only for its other type parameters, so
# the task's root takes the call's last arguments as witnesses of those alone
job(t:type) := class<abstract>:
    Run()<suspends>:t
    With(X:u, ?Us:[]u = array{} where u:type)<suspends>:tuple(t, u)
pairJ(a:type, b:type) := class(job(a)):
    A:a
    B:b
    Run<override>()<suspends>:a =
        Sleep(0.1)
        A
    With<override>(X:u, ?Us:[]u = array{} where u:type)<suspends>:tuple(a, u) =
        Sleep(0.1)
        Seen:b = B
        (A, X)
    Both()<suspends>:tuple(a, b) =
        Sleep(0.2)
        (A, B)
    Kick():task(a) = spawn{Run()}
# (a class whose type parameter its parent's type arguments do not mention)
hidJ(a:type) := class(job(int)):
    W:a
    N:int
    Run<override>()<suspends>:int =
        Sleep(0.1)
        N
    With<override>(X:u, ?Us:[]u = array{} where u:type)<suspends>:tuple(int, u) = (N + Us.Length, X)
# (from code generic over the class's own type parameters)
Go(P:pairJ(t, s) where t:type, s:type)<suspends>:tuple(t, s) =
    T := spawn{P.Both()}
    U := spawn{P.With(P.B)}
    (T.Await()(0), U.Await()(1))
Main()<suspends>:void =
    P := pairJ(int, string){A := 4, B := "x"}
    T1 := spawn{P.Run()}
    T2 := spawn{P.With(2)}
    T3 := spawn{P.With("y", ?Us := array{"z"})}
    Print("{T1.Await()} {T2.Await()(1)} {T3.Await()(1)}")
    G := Go(pairJ(logic, int){A := true, B := 7})
    Print("{G(1)}")
    H := hidJ(string){W := "w", N := 5}
    T4 := spawn{H.Run()}
    T5 := spawn{H.With(1.5, ?Us := array{2.5, 3.5})}
    Print("{T4.Await()} {T5.Await()(0)}")
    # (an immediate method's spawn of its class's own method, and a cancel)
    K := P.Kick()
    T6 := spawn{P.Both()}
    T6.Cancel()
    Print("{K.Await()}")

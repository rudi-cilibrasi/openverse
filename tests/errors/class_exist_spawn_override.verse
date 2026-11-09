# expect: a spawn in an override of a class with type parameters that its parent's type arguments do not give
Worker()<suspends>:int =
    Sleep(1.0)
    7
expr(t:type) := class<abstract>:
    Start():task(int)
pairE(a:type, b:type) := class(expr(tuple(a, b))):
    A:a
    B:b
    Start<override>():task(int) = spawn{Worker()}
Main()<suspends>:void =
    P := pairE(int, string){A := 1, B := "s"}
    Print("{P.Start().Await()}")

# expect: a spawn of pairJ.Run, a method of a class with type parameters that its parent's type arguments do not give, is not supported yet (#209)
# (spawned through the class above, J:job(int) = P then spawn{J.Run()}, it runs)
job(t:type) := class<abstract>:
    Run()<suspends>:t
pairJ(a:type, b:type) := class(job(a)):
    A:a
    B:b
    Run<override>()<suspends>:a =
        Sleep(0.1)
        A
Main()<suspends>:void =
    P := pairJ(int, string){A := 4, B := "x"}
    J:job(int) = P
    T := spawn{P.Run()}
    Print("{T.Await()}")

# Spawns in immediate functions reached at opened type arguments (#209):
# an immediate override that spawns, a generic immediate function that
# spawns at its type parameters (called from overrides, from a cast branch,
# and under polymorphic recursion).
Worker()<suspends>:int =
    Sleep(1.0)
    7
expr(t:type) := class<abstract>:
    Start():task(int)
pairE(a:type, b:type) := class(expr(tuple(a, b))):
    A:a
    B:b
    Start<override>():task(int) = spawn{Worker()}

job(t:type) := class<abstract>:
    Run()<suspends>:t
Echo(X:t where t:type)<suspends>:t = X
Kick(X:t where t:type):task(t) = spawn{Echo(X)}
gj(t:type) := class(job(t)):
    V:t
    Run<override>()<suspends>:t = Kick(V).Await()
pairJ(a:type, b:type) := class(job(tuple(a, b))):
    L:job(a)
    R:job(b)
    Run<override>()<suspends>:tuple(a, b) =
        T := spawn{L.Run()}
        X := R.Run()
        K := Kick(X)
        (T.Await(), K.Await())

lit := class(job(int)):
    V:int
    Run<override>()<suspends>:int =
        Sleep(0.1)
        Print("lit {V}")
        V
Probe(J:job(t) where t:type):int =
    if (P := pairJ[J]):
        TL := spawn{P.L.Run()}
        2
    else:
        1

Grow(J:job(t), N:int where t:type)<suspends>:int =
    T := spawn{J.Run()}
    Y := T.Await()
    if (N > 0) then Grow(gj(tuple(t, t)){V := (Y, Y)}, N - 1) else N

Main()<suspends>:void =
    P := pairE(int, string){A := 1, B := "s"}
    Print("{P.Start().Await()}")
    J:job(tuple(int, string)) = pairJ(int, string){L := gj(int){V := 1}, R := gj(string){V := "two"}}
    Q := J.Run()
    Print("{Q(0)} {Q(1)}")
    K:job(tuple(int, int)) = pairJ(int, int){L := lit{V := 3}, R := lit{V := 4}}
    Print("{Probe(K)}")
    Sleep(0.5)
    Print("{Grow(gj(int){V := 1}, 3)}")

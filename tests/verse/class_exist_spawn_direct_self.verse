# a spawn of Self's method inside an immediate override of a class with type
# parameters that its parent's type arguments do not give (#209): the task's
# root is generic at the override's type parameters, which it reads from its
# receiver, so its slots of those types (Run's result, tuple(a, b)) start as
# the receiver's hidden fields, as the override's own do (a probe from the
# review of #316)
job(t:type) := class<abstract>:
    Run()<suspends>:t
    Go():task(t)
lit := class(job(int)):
    V:int
    Run<override>()<suspends>:int =
        Sleep(0.1)
        V
    Go<override>():task(int) = spawn{Run()}
pairJ(a:type, b:type) := class(job(tuple(a, b))):
    L:job(a)
    R:job(b)
    Run<override>()<suspends>:tuple(a, b) = (L.Go().Await(), R.Go().Await())
    Go<override>():task(tuple(a, b)) = spawn{Run()}
Main()<suspends>:void =
    J:job(tuple(int, tuple(int, int))) = pairJ(int, tuple(int, int)){L := lit{V := 1}, R := pairJ(int, int){L := lit{V := 2}, R := lit{V := 3}}}
    Q := J.Go().Await()
    Print("{Q(0)} {Q(1)(0)} {Q(1)(1)}")

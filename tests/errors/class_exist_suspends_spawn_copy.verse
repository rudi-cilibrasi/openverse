# expect: needs a copy per type (#174), and its class has type parameters that its parent's type arguments do not give
job(t:type) := class<abstract>:
    Run()<suspends>:t
lit := class(job(int)):
    V:int
    Run<override>()<suspends>:int = V
Helper(J:job(u) where u:type)<suspends>:void =
    T := spawn{J.Run()}
idJ(a:type, b:type) := class(job(a)):
    L:job(a)
    R:job(b)
    Run<override>()<suspends>:a =
        Helper(L)
        L.Run()
Main()<suspends>:void =
    J:job(int) = idJ(int, int){L := lit{V := 1}, R := lit{V := 2}}
    Print("{J.Run()}")

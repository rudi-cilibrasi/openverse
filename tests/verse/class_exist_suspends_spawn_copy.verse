# a spawned dispatch at the type parameters of a function an opened override
# calls: lifted into a generic `$dispatchK` before the specialisation, a root at
# the caller's type arguments (#244), not a copy per type (#209)
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

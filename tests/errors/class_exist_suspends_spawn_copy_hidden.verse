# expect: needs a copy per type (#174), and its class has type parameters that its parent's type arguments do not give
# (an override whose only type parameter is held by its receiver: idJ(a) := class(job(int)))
job(t:type) := class<abstract>:
    Run()<suspends>:t
lit := class(job(int)):
    V:int
    Run<override>()<suspends>:int = V
Helper(J:job(u) where u:type)<suspends>:void =
    T := spawn{J.Run()}
idJ(a:type) := class(job(int)):
    L:job(a)
    Run<override>()<suspends>:int =
        Helper(L)
        7
Main()<suspends>:void =
    J:job(int) = idJ(int){L := lit{V := 1}}
    Print("{J.Run()}")

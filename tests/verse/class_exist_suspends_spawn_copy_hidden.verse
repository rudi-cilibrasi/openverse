# the same, in an override whose only type parameter its receiver holds (#209)
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

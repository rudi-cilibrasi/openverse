# expect: 6:8: set through a map's key can fail
# A for's body is no failure context: a set through a map's key there is refused (its clauses are one).
Main():void =
    var M:[int]int = map{}
    for (I := 1..3):
        set M[I] = I

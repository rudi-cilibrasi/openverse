# expect: 5:27: return cannot leave a failure context
# A return in a for's clauses (its body may return: Return.versetest:152)
F(Xs:[]int):int =
    var S:int = 0
    for (X : Xs, X > 0 or (return S)) { set S += X }
    S
Main():void = Print("{F(array{1, 2})}")

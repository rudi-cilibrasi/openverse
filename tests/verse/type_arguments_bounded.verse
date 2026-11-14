# A bounded type given as an argument (the Book's tests: FORT-1059276.versetest:6,
# Foo(t:castable_subtype(c), Xs:[]t); ParametricTypes.versetest 1305-1329,
# F(X:int, t:type, u:subtype(t), Y:t, Z:u)): a bounded type parameter (#502).
shape := class:
    Sides:int = 0
square := class(shape):
    Sides<override>:int = 4
Count(t:subtype(shape), Xs:[]t):int =
    var N:int = 0
    for (X : Xs):
        set N += X.Sides
    N
tagged := class<castable>:
    Tag:int = 7
Tags(t:castable_subtype(tagged), Xs:[]t):int =
    var N:int = 0
    for (X : Xs):
        set N += X.Tag
    N
Pick(X:int, t:type, u:subtype(t), Y:t, Z:u):t =
    if (X = 1):
        Y
    else:
        Z
Main():void =
    Print(ToString(Count(square, array{square{}, square{}})))
    Print(ToString(Count(shape, array{shape{}, square{}})))
    Print(ToString(Tags(tagged, array{tagged{}, tagged{}})))
    P := Pick(2, shape, square, shape{}, square{})
    Print(ToString(P.Sides))

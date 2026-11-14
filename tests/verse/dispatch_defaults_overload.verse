base(t:type) := class:
    F(X:[]t,?N:int=0):int=N
    F(X:int,?Scalar:logic,?N:int=0):int=N
ib := class(base(int)):
    Seed:int=4
    F<override>(X:[]int,?N:int=Seed+X.Length):int=N
    F<override>(X:int,?Scalar:logic,?N:int=Seed+X):int=N
# (base only takes t in, so a base(t) gives no t, the Book's rule,
# ParametricFunctions.versetest 356: the type is given as an argument)
Run(t:type, P:base(t)):void=
    Print("{P.F(array{})}")
    Print("{P.F(7,?Scalar:=true)}")
Main():void=Run(int, ib{})

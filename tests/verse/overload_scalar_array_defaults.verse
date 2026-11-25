# Overloaded methods on []t and int, each with a default the dispatch fills
# (#724): one argument is no tuple of the arguments, so the two are distinct,
# as F(:a) beside F(:[]a) is (tests/verse/overload_scalar_array; the refusal
# this program pinned since #510 was openverse's own).
base(t:type) := class:
    F(X:[]t,?N:int=0):int=N
    F(X:int,?N:int=0):int=N
ib := class(base(int)):
    Seed:int=4
    F<override>(X:[]int,?N:int=Seed+X.Length):int=N
    F<override>(X:int,?N:int=Seed+X):int=N
Run(t:type, P:base(t)):void=
    Print("{P.F(array{})}")
    Print("{P.F(7)}")
Main():void=Run(int, ib{})

# An unnamed parameter, F(:t), as function types write one (Book of Verse
# ch. 6: `F(:int):void = {}`): a parameter of type t that the body cannot
# name. A parameter written as a function's signature may also stand in a
# function type's parameters, `A(F(:int):int, X:int):int`. A parametric
# type's parameter may be unnamed too, `tagged(:type)`.
VoidInput(:void):int = 19
Pick(:int, Y:int):int = Y
Apply(F(:int):int, X:int):int = F(X)
Twice(A(F(:int):int, X:int):int, X:int):int = A(Inc, A(Inc, X))
Pair((:int, Y:int)):int = Y
c := class:
    M(:int):int = 3
tagged(:type) := class:
    N:int = 4
Inc(X:int):int = X + 1
Main():void =
    Print("{VoidInput(1)} {Pick(1, 2)} {Apply(Inc, 4)} {Twice(Apply, 5)} {Pair((8, 9))} {c{}.M(9)} {tagged(int){}.N}")

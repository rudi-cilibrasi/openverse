# tuples as arrays (Book of Verse ch. 3): a tuple converts to an array of its
# elements where an array is expected, and compares with an array as one

shape := class:
    N:int = 1
square := class(shape):
    M:int = 2

Sum(Xs:[]int):int =
    var S:int = 0
    for (X : Xs) { set S += X }
    S

Len(Xs:[]t where t:type):int = Xs.Length

Main():void =
    A:[]int = (1, 2, 3)
    Print("{A.Length} {Sum(A)} {Sum((4, 5))}")
    if (array{1, 2} = (1, 2)) then Print("equal") else Print("unequal")
    if ((1, 2) = array{1, 2}) then Print("equal") else Print("unequal")
    if (array{1, 2} = (2, 1)) then Print("equal") else Print("unequal")
    Shapes:[]shape = (shape{}, square{})
    for (Sh : Shapes) { Print("{Sh.N}") }
    S:string = ('h', 'i')
    Print(S)
    # (#108 review) chains, element types from the array, inference, joins
    T := array{1, 2}
    if (T = (1, 2) = T) then Print("chain equal") else Print("chain unequal")
    O:[]?int = (false, option{3})
    N:[][]int = (array{}, array{1})
    Print("{O.Length} {N.Length}")
    Print("{Len((7, 8, 9))}")
    B:logic = true
    J:[]int = if (B?) then (1, 2) else array{3}
    Print("{J.Length}")
    P:tuple(int, []int) = (1, (2, 3))
    Print("{P(1).Length}")

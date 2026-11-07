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

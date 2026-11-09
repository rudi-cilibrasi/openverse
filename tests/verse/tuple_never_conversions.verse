# a tuple or array with an element that never gives a value (`return`),
# converted: to an array, spread into a call's arguments, through option{}
# with a declared type, as an array literal in `not`, and an array of such
# elements to []int (#290): the element left before the conversion runs
Arr(K:int):int =
    if (K = 2):
        A:[]int = (1, return 42)
        return A.Length
    0
Add(X:int, Y:int):int = X + Y
Spread(K:int):int =
    if (K = 2) then return Add((return 9, 3))
    0
Opt(K:int):int =
    O:?tuple(int, int) = option{(K = 2, return 77)}
    if (P := O?) then P(0) else 0
Lit(K:int):int =
    if (not (K = 2, array{return 42})) then 7 else 8
Elems(K:int):int =
    if (K = 2):
        X := array{return 42}
        Y:[]int = X
        return Y.Length
    0
Main():void =
    Print("{Arr(2)} {Arr(3)}")
    Print("{Spread(2)} {Spread(3)}")
    Print("{Opt(2)} {Opt(3)}")
    Print("{Lit(2)} {Lit(3)}")
    Print("{Elems(2)} {Elems(3)}")

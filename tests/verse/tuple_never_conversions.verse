# a tuple or array with an element that never gives a value (`return`),
# converted: to an array, spread into a call's arguments, as an array literal
# in an if's branch, and an array of such elements to []int (#290): the
# element left before the conversion runs. (In option{} or `not`, failure
# contexts, the return could not leave them: the Book of Verse's tests,
# Reachability.versetest:12.)
Arr(K:int):int =
    if (K = 2):
        A:[]int = (1, return 42)
        return A.Length
    0
Add(X:int, Y:int):int = X + Y
Spread(K:int):int =
    if (K = 2):
        R := Add((return 9, 3))
        return R
    0
Lit(K:int):int =
    A := if (K = 2) then array{return 42} else array{7}
    if (V := A[0]) then V else 8
Elems(K:int):int =
    if (K = 2):
        X := array{return 42}
        Y:[]int = X
        return Y.Length
    0
# (review) a concatenation of a loop that only returns, a map of such values
# to [int]any
Cat(K:int):int =
    var A:[]int = array{1, 2}
    set A += for (I := 0..3, I > K) { return I }
    A.Length
AnyMap(K:int):int =
    M := if (K = 2) then map{1 => return 5} else map{2 => any(3)}
    M.Length
Main():void =
    Print("{Arr(2)} {Arr(3)}")
    Print("{Spread(2)} {Spread(3)}")
    Print("{Lit(2)} {Lit(3)}")
    Print("{Elems(2)} {Elems(3)}")
    Print("{Cat(2)} {Cat(5)}")
    Print("{AnyMap(2)} {AnyMap(3)}")


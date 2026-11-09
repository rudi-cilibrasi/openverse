# values that never come (#297): a tuple with a `return` element spread into
# a method, a generic function and a function value; maps of such values
# converted to [int]int and to a class; and an array literal joining such an
# element with an int, in `not`
c := class:
    B:int
    Add(X:int, Y:int):int = X + Y + B
Pair(X:t, Y:t where t:type):t = Y
Add(X:int, Y:int):int = X + Y
Meth(K:int):int =
    O := c{B := 100}
    if (K = 2) then return O.Add((return 9, 3))
    O.Add((K, 3))
Gen(K:int):int =
    if (K = 2) then return Pair((return 9, 3))
    Pair((K, 3))
Val(K:int):int =
    G := Add
    if (K = 2) then return G((return 9, 3))
    G((K, 3))
box := class:
    V:int
Maps(K:int):int =
    M := if (K = 2) then map{1 => return 5} else map{2 => 3}
    N := if (K = 2) then map{1 => return 6} else map{2 => box{V := 4}}
    M.Length + N.Length
Mix(K:int):int =
    if (not (K = 2, array{return 1, 5})) then 7 else 8
# (review) such values read from a tuple, taken to `any` where the type is
# inferred; a mixed array literal with a string
ToAny(K:int):int =
    A := for (I := 0..3, I > K) { return I }
    var N:int = 0
    for (Y : A) { set N += array{any(Y), any(2)}.Length }
    N
MixStr(K:int):int =
    if (not (K = 2, array{return 1, "a"})) then 7 else 8
Main():void =
    Print("{Meth(2)} {Meth(3)} {Gen(2)} {Gen(3)} {Val(2)} {Val(3)}")
    Print("{Maps(2)} {Maps(3)} {Mix(2)} {Mix(3)}")
    Print("{ToAny(5)} {ToAny(1)} {MixStr(2)} {MixStr(3)}")

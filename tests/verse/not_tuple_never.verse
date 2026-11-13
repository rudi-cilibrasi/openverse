# `return` as an element of a tuple with an expected type (#285), and joined.
# (Such an element in the tuple `not` tests, or in the left of `or`, which #285
# also took, would leave a failure context, which the Book of Verse's tests
# refuse: Reachability.versetest:12, SOL-4199-BreakFromIf.versetest.)
# with an expected type, such an element is checked against it, as before
Typed(K:int):int =
    T:tuple(int, int) = (1, if (K = 2) then return 3 else K)
    T(1)
# a tuple with such an element joined with another, in an if's branch and an
# array: taken to the joined type, the element is as it was
Joined(K:int):int =
    T := if (K > 5) then (Err(), 0) else (1, 2)
    U := if (K = 2) then (K, return 42) else (K, 3)
    A := array{(K, if (K = 9) then return 9 else K), (3, 4)}
    if (X := A[0]) then T(1) + U(1) + X(1) else 0
Main():void =
    Print("{Typed(2)} {Typed(5)}")
    Print("{Joined(2)} {Joined(3)}")

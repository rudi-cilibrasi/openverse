# expect: more than 500 copies of generic functions with branch, rush or spawn
Grow(X:t, N:int where t:type)<suspends>:int =
    branch:
        Sleep(1.0)
    if (N > 0) then Grow(array{X}, N - 1) else 0
Main()<suspends>:void = Print("{Grow(1, 3)}")

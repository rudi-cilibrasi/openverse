# polymorphic recursion, doubling, with a branch: the branch is a root of the
# scheduler at the function's type arguments, which its dispatch opens (#244)
Grow(X:t, N:int where t:type)<suspends>:int =
    branch:
        Sleep(1.0)
    if (N > 0) then Grow((X, X), N - 1) else 0
Main()<suspends>:void = Print("{Grow(1, 3)}")

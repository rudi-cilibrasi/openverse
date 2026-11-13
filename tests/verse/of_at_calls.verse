# `F of X` is `F(X)` and `F at X` is `F[X]` (Book of Verse tests,
# Operators/Of.versetest, Operators/At.versetest): the argument in braces, a
# body after `:` or `.`, or an operand; `F of {X:int}:t` defines a function
SomeFuncThatTakesInt(I : int) : int = I
SomeFuncThatTakesArray(A : []int) : int =
    var Result : int = 0
    for (E : A):
        set Result += E
    return Result
Pick(A : []int)<decides> : int = A[1]
Twice(A : int)<decides> : int = A * 2
TwoArgs(I : int, F : float) : float = 1.0 * I + F
Defined of {I:int} : int = I * 3
F1(A:int):int = A*10
Main():void =
    A := SomeFuncThatTakesInt of {42}
    B := SomeFuncThatTakesInt of 43
    C := SomeFuncThatTakesInt of:
        44
    D := SomeFuncThatTakesInt of. 45
    E := SomeFuncThatTakesArray of array:
        42
        -13
        53
        10
    G := TwoArgs of:
        (1, 2.5)
    H := F1 of (4;5)
    if (P := Pick at array{7, 8, 9}, Q := Twice at:
        21
    ):
        Print("{A} {B} {C} {D} {E} {G} {H} {P} {Defined(4)} {Defined of 5} {Q}")

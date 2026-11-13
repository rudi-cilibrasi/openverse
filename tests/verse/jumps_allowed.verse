# The returns and breaks the Book of Verse allows: none leaves a failure
# context (an if's conditions, a for's clauses, first, option{}, logic{},
# not, the left of or), and in a <decides> function, whose body is one, a
# return is in tail position (Return.versetest 136-160)
# a return in an if's branch, and in a for's body
Find(Xs:[]int, Y:int):int =
    for (I -> X : Xs):
        if (X = Y) then return I
    -1
# a break in an if's branch, after its condition succeeded
Count(Limit:int):int =
    var N:int = 0
    loop:
        set N += 1
        if (N * N > Limit, N > 2):
            break
    N
# a <decides> function's returns in tail position: the body, the branches
# of its last if, the arms of its last case, a return's value
Sign(X:int)<decides>:int =
    if (X > 0):
        return 1
    else if (X < 0):
        return -1
    else:
        X = 0
        return 0
Pick(X:int)<decides>:int =
    case (X):
        1 => return 10
        2 => 20
        _ => return X * 100
Same(X:int)<decides>:int = return X
# a loop in a <decides> function, left by a break in a branch
Steps(X:int)<decides>:int =
    X > 0
    var N:int = X
    loop:
        if (N >= 10) then break
        set N *= 2
    N
Main():void =
    Print("{Find(array{4, 5, 6}, 5)} {Find(array{4}, 9)} {Count(10)}")
    if (A := Sign[3], B := Sign[-2], C := Sign[0]) then Print("{A} {B} {C}")
    if (A := Pick[1], B := Pick[2], C := Pick[3]) then Print("{A} {B} {C}")
    if (A := Same[7], B := Steps[3]) then Print("{A} {B}")
    if (not Steps[0]) then Print("no steps")

# loop, break and return (Book of Verse ch. 7).
FirstAbove(A:[]int, T:int):int =
    for (X : A):
        if (X > T) { return X }
    -1

Collatz(N:int):int =
    var Steps:int = 0
    var X:int = N
    loop:
        if (X = 1) { break }
        if (Mod[X, 2] = 0):
            set X = Quotient[X, 2] or 0
        else:
            set X = 3 * X + 1
        set Steps += 1
    Steps

Main():void =
    Print("first above 3: {FirstAbove(array{1, 5, 2, 7}, 3)}")
    Print("first above 9: {FirstAbove(array{1, 5, 2, 7}, 9)}")
    Print("Collatz(27) takes {Collatz(27)} steps")

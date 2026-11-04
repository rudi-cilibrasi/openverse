# Classic algorithms written in idiomatic Verse.

# Insertion sort on an immutable array, rebuilt through var and set A[i].
Sort(Input:[]int):[]int =
    var A:[]int = Input
    for (I := 1..A.Length - 1):
        var J:int = I
        loop:
            if (J > 0, Prev := A[J - 1], Cur := A[J], Prev > Cur):
                if (set A[J] = Prev, set A[J - 1] = Cur) {}
                set J -= 1
            else:
                break
    A

# Binary search: fails when the value is absent.
Find(A:[]int, X:int)<decides>:int =
    var Lo:int = 0
    var Hi:int = A.Length - 1
    var Found:int = -1
    loop:
        if (Lo > Hi) { break }
        Mid := Floor((Lo + Hi) / 2) or 0
        if (V := A[Mid]):
            if (V = X):
                set Found = Mid
                break
            else if (V < X):
                set Lo = Mid + 1
            else:
                set Hi = Mid - 1
        else:
            break
    Found >= 0
    Found

IsPrime(N:int)<decides>:void =
    N >= 2
    not (for (D := 2..N - 1, D * D <= N, Mod[N, D] = 0) { D })[0]

Reverse(S:string):string =
    var R:string = ""
    for (C : S) { set R = array{C} + R }
    R

Join(A:[]int):string =
    var S:string = ""
    for (I -> X : A):
        if (I > 0) { set S += ", " }
        set S += "{X}"
    S

FizzBuzz(N:int):string =
    if (Mod[N, 15] = 0) then "FizzBuzz"
    else if (Mod[N, 3] = 0) then "Fizz"
    else if (Mod[N, 5] = 0) then "Buzz"
    else "{N}"

Main():void =
    Sorted := Sort(array{5, 3, 9, -2, 7, 3, 0})
    Print("sorted: {Join(Sorted)}")
    if (I := Find[Sorted, 7]) { Print("7 is at index {I}") }
    if (not Find[Sorted, 4]) { Print("4 is not there") }
    Primes := for (N := 1..30, IsPrime[N]) { N }
    Print("primes: {Join(Primes)}")
    Print("reversed: {Reverse("stressed")}")
    for (N := 9..15) { Print(FizzBuzz(N)) }

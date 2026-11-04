# Arrays are immutable values; var rebinding and set A[i] (Book of Verse ch. 3, 5).
Sum(A:[]int):int =
    var S:int = 0
    for (X : A) { set S += X }
    S

Main():void =
    var C:[]int = array{1, 2, 3}
    D := C
    set C += array{4}
    if (set C[0] = 10) { Print("set C[0] succeeded") }
    if (not (set C[10] = 1)) { Print("set C[10] fails: out of range") }
    Print("C has {C.Length} elements, sum {Sum(C)}; D still sums to {Sum(D)}")
    if (X := C[1]) { Print("C[1] = {X}") }
    if (not C[4]) { Print("C[4] fails") }
    S:string = "Verse" + "!"
    Print("{S} has length {S.Length}")
    if ("abc" = "abc") { Print("strings compare by value") }
    if (array{1, 2} <> array{2, 1}) { Print("order matters") }
    T := (1, "two", 'c')
    Print("tuple: {T(0)} {T(1)} {T(2)}")
    var E:[]int = false
    Print("empty: {E.Length}")
